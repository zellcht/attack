#include "attack.h"
#include "stdio.h"


#define BUFFER_SIZE ( 80 )

pid_t pid        = 0;    // process ID (of either parent or child) from fork

int   target_raw[ 2 ];   // unbuffered communication: attacker -> attack target
int   attack_raw[ 2 ];   // unbuffered communication: attack target -> attacker

FILE* target_out = NULL; // buffered attack target input  stream
FILE* target_in  = NULL; // buffered attack target output stream

typedef unsigned char octet;

void computefec(mpz_t fec, mpz_t f1, mpz_t n, mpz_t e, mpz_t c);
void mpz2octet(octet *em, mpz_t m);
void getblock(octet *em_part, octet *em, int start_point, int length);
void I2OSP(octet *C, int x, int xLen);
void mgf(octet *mask, octet *mgfSeed, int length, int maskLen, int hLen);
void xor(octet *r, octet *x, octet *y, int length);
void getMfromDB(octet *M, octet *DB, int hLen, int length);
void computeUID(octet *M);
/* interact with D.
 * Send c to D, and get the error code.
 *
 * @param r_code Error code
 * @param c Ciphertext
 */
void interact(int* r_code, mpz_t c ) {

  // Send c to D.
  gmp_fprintf( target_in, "%0256Zx\n", c );  

  fflush( target_in );

  // Receive r_code from D.
  int unused __attribute__((unused));
  unused = fscanf( target_out, "%d", r_code );

}

void attack(mpz_t n, mpz_t e, mpz_t c) {
  int k, exp, r_code,em_len,hLen;
  mpz_t b, f1, fec, n_b, f2, f1_h, f3, min, max, ftmp, i, in, in_b, b2, temp;
  mpz_inits(b, f1, fec, n_b, f2, f1_h, f3, min, max, ftmp, i, in, in_b, b2, temp, NULL);
  k = mpz_sizeinbase(n, 256);
  printf("k = %d\n",k);
  exp = 8 * (k-1);
  mpz_ui_pow_ui(b, 2, exp);
  
  /* Step 1 */
  printf("step 1...\n");

  mpz_set_ui(f1, 2);
  while(1){ 
    computefec(fec, f1, n, e, c);
    interact(&r_code, fec);
    if(r_code == 1){
      break;
    }
    mpz_mul_ui(f1, f1, 2);
  }

  /* Step 2 */
  printf("step 2...\n");

  mpz_add(n_b, n, b);
  mpz_fdiv_q(n_b, n_b, b);
  mpz_fdiv_q_ui(f1_h, f1, 2);
  mpz_mul(f2, n_b, f1_h);

  while(1){
    computefec(fec, f2, n, e, c);
    interact(&r_code, fec);
    if(r_code == 2){
      break;
    }
    mpz_add(f2, f2, f1_h);
  }
  /* Step 3 */
  printf("step 3...\n");

  mpz_add(n_b, n, b);
  mpz_mul_ui(b2, b, 2);
  mpz_cdiv_q(min, n, f2);
  mpz_fdiv_q(max, n_b, f2);

  while(mpz_cmp(min, max) != 0){
    
    mpz_sub(temp, max, min);
    mpz_fdiv_q(ftmp, b2, temp);
    mpz_mul(ftmp, ftmp, min);
    mpz_fdiv_q(i, ftmp, n);
    mpz_mul(in, i, n);
    mpz_cdiv_q(f3, in, min);
    
    computefec(fec, f3, n, e, c);
    interact(&r_code, fec);

    mpz_add(in_b, in, b);
    if(r_code == 1){
      mpz_cdiv_q(min, in_b, f3);
    }
    else if(r_code == 2){
      mpz_fdiv_q(max, in_b, f3);
    }
  }
  
  mpz_powm(fec, max, e, n);
  interact(&r_code, fec);

  printf("Result code: %d \n",r_code);

  em_len = mpz_sizeinbase (max, 256);
  hLen = 20;
  octet emOctets[em_len], maskedSeed[hLen], maskedDB[k-hLen-1], seedMask[hLen], seed[hLen], dbMask[k-hLen-1], DB[k-hLen-1], M[k-hLen-1];
  
  mpz2octet(emOctets, max);    
  printf("Get maskedSeed...\n");
  memset(maskedSeed, 0, hLen);
  memcpy(maskedSeed, emOctets+1, hLen);
  printf("Get maskedDB...\n");
  memset(maskedDB, 0, k-hLen-1);
  memcpy(maskedDB, emOctets+hLen+1, k-hLen-1);
  
  printf("Get DB...\n");
  mgf(seedMask,maskedDB, k-hLen-1, hLen, hLen);  
  xor(seed, maskedSeed, seedMask, hLen);
  mgf(dbMask, seed, hLen, k-hLen-1, hLen);  
  xor(DB, maskedDB, dbMask, k-hLen-1);
  
  printf("Get M...\n");
  
  getMfromDB(M, DB, hLen, k-hLen-1);
  computeUID(M);
  mpz_clears(b, f1, fec, n_b, f2, f1_h, f3, min, max, ftmp, i, in, in_b, b2, temp, NULL);
  
}

void computeUID(octet *M){
  long sum,tmp;
  sum = 0;
  for(int i =  0; i < 4; i++){
    tmp = pow(2, 8 * i);
    tmp = M[i] * tmp;
    sum = sum + tmp;
  }
  printf("UID : %ld\n",sum);
}
/* compute f^e * c mod N */
void computefec(mpz_t fec, mpz_t f, mpz_t n, mpz_t e, mpz_t c){

  mpz_powm(fec, f, e, n);
  mpz_mul(fec, fec, c);
  mpz_mod(fec, fec, n);

}
/* transfer mpz into octet */
void mpz2octet(octet *em, mpz_t m){
  mpz_t  rm;	
  mpz_inits(rm,NULL);
  int m_len;
  octet r;
  r= '0';
  em[0] = r;
  m_len = mpz_sizeinbase(m, 256);
  
  for(int i = m_len; i > 0; i--){
    mpz_mod_ui(rm, m, 256);
    r = mpz_get_ui(rm);
    em[i]= r;
    mpz_fdiv_q_ui(m, m, 256);
  }
  mpz_clear(rm);
}

/* transfer int into octet */
void I2OSP(octet *C, int x, int xLen){
  mpz_t x_t, max, rm;
  mpz_inits(x_t, max, rm, NULL);
  octet r;
  mpz_set_ui(x_t, x);
  mpz_ui_pow_ui(max, 256, xLen);
  
  if(mpz_cmp(x_t, max) >= 0){
    printf("integer too large\n");
    exit(1);
  }
  for(int i = 0; i < xLen; i++){
    mpz_mod_ui(rm, x_t, 256);
    r = mpz_get_ui(rm);
    C[xLen-i-1] = r;
    mpz_fdiv_q_ui(x_t, x_t, 256);
  }
  mpz_clears(x_t, max, rm, NULL);
}
/* Mask Generation Functions */
void mgf(octet *mask, octet *mgfSeed, int length, int maskLen, int hLen){
  mpz_t mask_len, h_len, hLen_max, temp;
  mpz_inits(mask_len, h_len, hLen_max, temp, NULL);
	
  octet C[4], sha1[20], T[1024], tmp[1024];
  int r;
  mpz_set_ui(mask_len, maskLen);
  mpz_set_ui(h_len, hLen);
  mpz_ui_pow_ui(temp, 2, 32);
  mpz_mul(hLen_max, temp, h_len);
  
  mpz_cdiv_q(temp, mask_len, h_len);
  r = mpz_get_ui(temp);
  
  if(mpz_cmp(mask_len, hLen_max) >= 0){
    printf("mask too long\n");
    exit(1);
  }

  for(int i = 0; i < r; i++){
    I2OSP(C, i, 4); 
    memset(tmp,0,1024);
    memcpy(tmp, mgfSeed, length);
    memcpy(tmp+length, C, 4);
    SHA1(tmp, length+4, sha1);
    memcpy((T+i*20), sha1, 20);
  }
  
  for(int i = 0; i < maskLen; i++){
    mask[i] = T[i];
  }
  mpz_clears(mask_len, h_len, hLen_max, temp, NULL);
}


void xor(octet *r, octet *x, octet *y, int length){
  
  for(int i = 0; i < length; i++){
    r[i] = (x[i] & ~y[i]) | (~x[i] & y[i]);
  }
}

/* Get the M from DB */
void getMfromDB(octet *M, octet *DB, int hLen, int length){
  int start;
  start = 0;
  for(int i = hLen; i < length; i++){
    if(DB[i] == 1){
      start = i+1;
    }
  }
  for(int i = 0; i < length - start; i++){
    M[i] = DB[i+start];
    printf("%x", M[i]);
  }
  printf("\n");
};


void cleanup( int s ){
  // Close the   buffered communication handles.
  fclose( target_in  );
  fclose( target_out );

  // Close the unbuffered communication handles.
  close( target_raw[ 0 ] ); 
  close( target_raw[ 1 ] ); 
  close( attack_raw[ 0 ] ); 
  close( attack_raw[ 1 ] ); 

  // Forcibly terminate the attack target process.
  if( pid > 0 ) {
    kill( pid, SIGKILL );
  }

  // Forcibly terminate the attacker      process.
  exit( 1 ); 
}
 
int main( int argc, char* argv[] ) {
  // Ensure we clean-up correctly if Control-C (or similar) is signalled.
  signal( SIGINT, &cleanup );
  // Create pipes to/from attack target; if it fails the reason is stored
  // in errno, but we'll just abort.
  if( pipe( target_raw ) == -1 ) {
    abort();
  }
  if( pipe( attack_raw ) == -1 ) {
    abort();
  }
  switch( pid = fork() ) { 
    case -1 : {
      // The fork failed; reason is stored in errno, but we'll just abort.
      abort();
    }
    case +0 : {
      // (Re)connect standard input and output to pipes.
      close( STDOUT_FILENO );
      if( dup2( attack_raw[ 1 ], STDOUT_FILENO ) == -1 ) {
        abort();
      }
      close(  STDIN_FILENO );
      if( dup2( target_raw[ 0 ],  STDIN_FILENO ) == -1 ) {
        abort();
      }

      // Produce a sub-process representing the attack target.
      execl( argv[ 1 ], "", NULL );

      // Break and clean-up once finished.
      break;
    }

    default : {
      // Construct handles to attack target standard input and output.
      if( ( target_out = fdopen( attack_raw[ 0 ], "r" ) ) == NULL ) {
        abort();
      }
      if( ( target_in  = fdopen( target_raw[ 1 ], "w" ) ) == NULL ) {
        abort();
      }

        FILE *public = NULL;
	
	mpz_t n,e,c;
	mpz_inits(n, e, c, NULL);

	public = fopen(argv[2],"r");
	mpz_inp_str(n, public, 16);
	mpz_inp_str(e, public, 16);
	mpz_inp_str(c, public, 16);
	fclose(public);

      // Execute a function representing the attacker.
	attack(n, e, c);

	mpz_clears(n, e, c, NULL);
      // Break and clean-up once finished.
      break;
    }
  }

  // Clean up any resources we've hung on to.
  cleanup( SIGINT );
  return 0;
}

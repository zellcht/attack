#include "attack.h"
#include "stdio.h"
#include <time.h>

pid_t pid        = 0;    // process ID (of either parent or child) from fork

int   target_raw[ 2 ];   // unbuffered communication: attacker -> attack target
int   attack_raw[ 2 ];   // unbuffered communication: attack target -> attacker

FILE* target_out = NULL; // buffered attack target input  stream
FILE* target_in  = NULL; // buffered attack target output stream

#define K 64
#define SIZE 4000
#define LENGTH 1024
#define DIFF 7
#define OBVIOUS 3

void sampleGen(mpz_t *c, mpz_t *m,int *T,const mpz_t N,const mpz_t e, int start, int end);
void mont_w(mpz_t w, const mpz_t mod);
void mont_p_2(mpz_t p_2, const mpz_t mod);
int mont_mul(mpz_t rop, const mpz_t op1, const mpz_t op2, const mpz_t mod);
void interact(int *time, mpz_t c );
void setBit(mpz_t d, mpz_t d_temp, mpz_t d_temp_m, int diff12, int diff34);

/* Generate samples.
 * encrypt with (N,e), and send to D to get the time.
 *
 * @param *m  Random generated m
 * @param *c  Encrypted m
 * @param *times The time get from D
 * @param N Modulo N
 * @param e Public key e
 * @param start Start point
 * @param end End point
 */
void sampleGen(mpz_t *c, mpz_t *m,int *times,const mpz_t N,const mpz_t e, int start, int end){
  mpz_t m_rand;
  mpz_inits(m_rand,NULL);
  gmp_randstate_t s;
  gmp_randinit_default (s);
  gmp_randseed_ui(s,time(NULL));
  
  int time;
  time = 0;
  for(int i = start; i < end; i++){	
    mpz_urandomb(m_rand,s, 1024);
    mpz_mod(m[i],m_rand,N);
    mpz_powm(c[i], m[i], e, N);
    interact(&time, c[i]);
    times[i] = time;  
  }
  mpz_clears(m_rand,NULL);
}
/* The function computes Montgomery parameter w(omega).
 * w = -mod^(-1) MOD b
 *
 * @param w    Result w.
 * @param mod  Modulo.
 */
void mont_w(mpz_t w, const mpz_t mod){
  mpz_t t,b;
  mpz_inits(t, b, NULL);
  mpz_set_ui(t, 1);
  mpz_ui_pow_ui(b,2,K);
  
  for(int i = 1; i < K; i++){
    mpz_mul(t, t, t);
    mpz_mul(t, t, mod);
    mpz_mod(t, t, b);
  }
  mpz_neg(t, t);
  mpz_mod(t, t, b);
  mpz_set(w, t);

  mpz_clears(t, b, NULL);
}

/* The function computes Montgomery parameter p^2.
 * p^2 = 2^(2*l(mod)*k)
 *
 * @param w    Result.
 * @param mod  Modulo.
 */
void mont_p_2(mpz_t p_2, const mpz_t mod){
  int e;
  mpz_t t;
  mpz_inits(t, NULL);
  mpz_set_ui(t, 1);
  size_t ln = mpz_size(mod);
  e = 2 * ln * K;
  for(int i = 1; i <= e; i++){
    mpz_add(t, t, t);
    mpz_mod(t, t, mod);
  }
  mpz_set(p_2, t);

  mpz_clears(t, NULL);
}

/* The function computes rop = op1 * op2 * p^(-1)
 * 
 * @param rop  Result.
 * @param op1  First oprand.
 * @param op2  Second oprand.
 * @param mod  Modulo.
 * @return reduction 1 if there is a reduction, 0 if not.
 */
int mont_mul(mpz_t rop, const mpz_t op1, const mpz_t op2, const mpz_t mod){
  int reduction;
  reduction = 0;
  unsigned long int r0,x0,yi;
  mpz_t a,b,w,p_2,u,t,r,x_0,y_i,r_0,temp;
  mpz_inits(a, b, w, p_2, u,t,r,x_0,y_i,r_0,temp,NULL);
  mpz_ui_pow_ui(b,2,K);
  mpz_set_ui(r, 0);
  mont_w(w, mod);
  size_t ln = mpz_size(mod);
  x0 = mpz_getlimbn(op1,0);
  mpz_set_ui(x_0, x0);
  for(int i = 0; i <= ln - 1; i++){
    yi =  mpz_getlimbn(op2,i);
    r0 =  mpz_getlimbn(r,0);
    mpz_set_ui(y_i, yi);
    mpz_set_ui(r_0, r0);

    mpz_mul(temp, x_0, y_i);
    mpz_add(u, temp, r_0);

    mpz_mul(u, w, u);
    mpz_mod(u, u, b);
 
    mpz_mul(t, y_i, op1);
    mpz_mul(a, u, mod);

    mpz_add(r,r,t);
    mpz_add(r,r,a);
    mpz_divexact(r, r, b);
  }
  if(mpz_cmp(r, mod) >= 0){
    mpz_sub(r, r, mod);
    reduction = 1;
  }
  else{
    reduction = 0;
  }
  mpz_set(rop, r);

  mpz_clears(a, b, w, p_2, u,t,r,x_0,y_i,r_0,temp,NULL);
  return reduction;
}
/* Send c to D, and get time from D.
 *
 * @param *time Time get from D.
 * @param c Ciphertext.
 */
void interact(int *time, mpz_t c ) {
  mpz_t m;
  mpz_init(m);
  // Send c to D.
  gmp_fprintf( target_in, "%0256Zx\n", c );  

  fflush( target_in );

  // Receive time from D.
  fscanf( target_out, "%d", time );
  gmp_fscanf( target_out, "%Zx", m );
}

void attack(mpz_t N, mpz_t e){
  mpz_t m[SIZE], c[SIZE], d, p_2, w, d_temp, d_temp_m, m_temp, m_temp_m, base, useless,mont_temp,mont_temp_m;
  mpz_inits(d, p_2, w, d_temp, d_temp_m, m_temp, m_temp_m, base, useless,mont_temp,mont_temp_m, NULL);

  for (int i=0;i<SIZE;i++){
    mpz_init(m[i]);
    mpz_init(c[i]);
  }
  int F1, F2, F3, F4, 
    F1_total, F2_total, F3_total, F4_total, 
    F1_avg, F2_avg, F3_avg, F4_avg, 
    diff12, diff34, diff1234, reduction, obvious, start_point, 
    times[SIZE];

  F1=0;
  F2=0;
  F3=0;
  F4=0;
  F1_total=0;
  F2_total=0;
  F3_total=0;
  F4_total=0;
  obvious = OBVIOUS;
  start_point = 1;
  
  mont_w(w, N);
  mont_p_2(p_2, N);
  
  /*First bit is 1*/
  mpz_set_ui(d, 1);

  printf("--Generating samples--\n");
  sampleGen(c, m, times, N, e, 0, SIZE);
  
  for(int k = 1;k < LENGTH;k++){
    printf("--Bit: %d--",k);
    for (int i=0;i<SIZE;i++){
      /* compute (m_temp * m)^2 */
      mpz_mul_ui(d_temp,d,2);

      mpz_add_ui(d_temp_m,d_temp,1);					
      mpz_powm(m_temp_m, c[i], d_temp_m, N);

      mont_mul(mont_temp_m,m_temp_m,p_2,N);
      reduction = mont_mul(useless,mont_temp_m,mont_temp_m,N);			
      
      if (reduction){
	F1 = F1 + times[i];
	F1_total++;
      }
      else{
	F2 = F2 + times[i];
	F2_total++;
      }
      /* compute (m_temp)^2 */
      mpz_powm(m_temp, c[i], d_temp, N);
      mont_mul(mont_temp,m_temp,p_2,N);
      reduction = mont_mul(useless,mont_temp,mont_temp,N);
      
      if (reduction){
	F3 = F3 + times[i];
	F3_total++;
      }
      else{
	F4 = F4 + times[i];
	F4_total++;
      }
      if (mpz_cmp(m_temp_m, m[i])==0){
	k=LENGTH;	
      }
    }
    /*Compute average*/
    F1_avg = F1 / F1_total;
    F2_avg = F2 / F2_total;
    F3_avg = F3 / F3_total;	
    F4_avg = F4 / F4_total;
    /*compute differnce*/
    diff12=abs(F1_avg-F2_avg);
    diff34=abs(F3_avg-F4_avg);
    diff1234 = abs(diff12-diff34);
    
    F1=0;
    F2=0;
    F3=0;
    F4=0;
    F1_total=0;
    F2_total=0;
    F3_total=0;
    F4_total=0;
    
    printf("--Diff12&34: %d--",diff1234);
    /* If the difference is not obvious, we still set the ki according to the diff12 and diff34. However, if It happens continuously, more than 3 times, we will back to the start point, and regenerates samples.*/
    if (diff1234 < DIFF){
      obvious--;
      printf("--%d not obvious--",OBVIOUS - obvious);
      if (!obvious){
	printf("--Regenerating samples--\n");
	sampleGen(c, m, times, N, e, 0, SIZE);
	mpz_divexact_ui(d, d_temp, 8); // 2^3.
	obvious = OBVIOUS;
	k=start_point;
      }
      else{
	setBit(d, d_temp, d_temp_m, diff12, diff34);
      }
    }
    else{
      obvious=OBVIOUS;
      start_point=k;
      setBit(d, d_temp, d_temp_m, diff12, diff34);
    }
  }

  gmp_printf("\n d : %ZX\n",d);
  
  for (int i=0;i<SIZE;i++){
    mpz_clear(m[i]);
    mpz_clear(c[i]);
  }
  mpz_clears(d, p_2, w, d_temp, d_temp_m, m_temp, m_temp_m, base, useless,mont_temp,mont_temp_m, NULL);
}

void setBit(mpz_t d, mpz_t d_temp, mpz_t d_temp_m, int diff12, int diff34){
  if (diff12>diff34){
    mpz_set(d,d_temp_m);		
    printf("--Bit : [1]--\n");		
  }
  else{
    mpz_set(d,d_temp);
    printf("--Bit : [0]--\n");
  }	
}


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


int main(int argc, char **argv){

  
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
      mpz_t N,e;
      mpz_inits(N,e,NULL);
      FILE *public;

      public = fopen(argv[2],"r");
      mpz_inp_str(N,public,16);
      mpz_inp_str(e,public,16);
      fclose(public);
      
      attack(N, e);

	break;
    }
  }
  
  // Clean up any resources we've hung on to.
  cleanup( SIGINT );
  
  return 0;
  
}





#include "attack.h"

#define SAMPLESIZE 50
#define KEYSIZE 256
#define TRACESIZE 3000
#define SIZE 33
#define NUM 100000
#define START 1000
#define END 4000

pid_t pid        = 0;    // process ID (of either parent or child) from fork

int   target_raw[ 2 ];   // unbuffered communication: attacker -> attack target
int   attack_raw[ 2 ];   // unbuffered communication: attack target -> attacker

FILE* target_out = NULL; // buffered attack target input  stream
FILE* target_in  = NULL; // buffered attack target output stream


typedef struct box{
  int sbox[256];
}box;


void computemid(int d[SAMPLESIZE], int key_hypo[KEYSIZE], int v[SAMPLESIZE][KEYSIZE]);
int simupower(int vij);
int computeorrelation(int v[SAMPLESIZE][KEYSIZE], int **trace, double trace_m[KEYSIZE], double v_m[SAMPLESIZE]);
void sampleGen(char m[SAMPLESIZE][SIZE], char c[SAMPLESIZE][SIZE], int **trace);
void interact(char *trace, char *c, char *m);
void computetrace(double trace_m[TRACESIZE], int **trace);
void getkey(char key[SIZE], char m[SAMPLESIZE][SIZE], int **trace, double trace_m[TRACESIZE]);

/* get S-box */
box getbox(){
  box b = {
    .sbox = {
      0x63, 0x7C, 0x77, 0x7B, 0xF2, 0x6B, 0x6F, 0xC5, 0x30, 0x01, 0x67, 0x2B, 0xFE, 0xD7, 0xAB, 0x76,
      0xCA, 0x82, 0xC9, 0x7D, 0xFA, 0x59, 0x47, 0xF0, 0xAD, 0xD4, 0xA2, 0xAF, 0x9C, 0xA4, 0x72, 0xC0,
      0xB7, 0xFD, 0x93, 0x26, 0x36, 0x3F, 0xF7, 0xCC, 0x34, 0xA5, 0xE5, 0xF1, 0x71, 0xD8, 0x31, 0x15,
      0x04, 0xC7, 0x23, 0xC3, 0x18, 0x96, 0x05, 0x9A, 0x07, 0x12, 0x80, 0xE2, 0xEB, 0x27, 0xB2, 0x75,
      0x09, 0x83, 0x2C, 0x1A, 0x1B, 0x6E, 0x5A, 0xA0, 0x52, 0x3B, 0xD6, 0xB3, 0x29, 0xE3, 0x2F, 0x84,
      0x53, 0xD1, 0x00, 0xED, 0x20, 0xFC, 0xB1, 0x5B, 0x6A, 0xCB, 0xBE, 0x39, 0x4A, 0x4C, 0x58, 0xCF,
      0xD0, 0xEF, 0xAA, 0xFB, 0x43, 0x4D, 0x33, 0x85, 0x45, 0xF9, 0x02, 0x7F, 0x50, 0x3C, 0x9F, 0xA8,
      0x51, 0xA3, 0x40, 0x8F, 0x92, 0x9D, 0x38, 0xF5, 0xBC, 0xB6, 0xDA, 0x21, 0x10, 0xFF, 0xF3, 0xD2,
      0xCD, 0x0C, 0x13, 0xEC, 0x5F, 0x97, 0x44, 0x17, 0xC4, 0xA7, 0x7E, 0x3D, 0x64, 0x5D, 0x19, 0x73,
      0x60, 0x81, 0x4F, 0xDC, 0x22, 0x2A, 0x90, 0x88, 0x46, 0xEE, 0xB8, 0x14, 0xDE, 0x5E, 0x0B, 0xDB,
      0xE0, 0x32, 0x3A, 0x0A, 0x49, 0x06, 0x24, 0x5C, 0xC2, 0xD3, 0xAC, 0x62, 0x91, 0x95, 0xE4, 0x79,
      0xE7, 0xC8, 0x37, 0x6D, 0x8D, 0xD5, 0x4E, 0xA9, 0x6C, 0x56, 0xF4, 0xEA, 0x65, 0x7A, 0xAE, 0x08,
      0xBA, 0x78, 0x25, 0x2E, 0x1C, 0xA6, 0xB4, 0xC6, 0xE8, 0xDD, 0x74, 0x1F, 0x4B, 0xBD, 0x8B, 0x8A,
      0x70, 0x3E, 0xB5, 0x66, 0x48, 0x03, 0xF6, 0x0E, 0x61, 0x35, 0x57, 0xB9, 0x86, 0xC1, 0x1D, 0x9E,
      0xE1, 0xF8, 0x98, 0x11, 0x69, 0xD9, 0x8E, 0x94, 0x9B, 0x1E, 0x87, 0xE9, 0xCE, 0x55, 0x28, 0xDF,
      0x8C, 0xA1, 0x89, 0x0D, 0xBF, 0xE6, 0x42, 0x68, 0x41, 0x99, 0x2D, 0x0F, 0xB0, 0x54, 0xBB, 0x16
    }
  };
  return b;
}
/* compute mid value and simulate power */
void computemid(int d[SAMPLESIZE], int key_hypo[KEYSIZE], int v[SAMPLESIZE][KEYSIZE]){	
  mpz_t d_z, key_hypo_z, v_ij;
  mpz_inits(d_z, key_hypo_z, v_ij, NULL);
  int v_ij_t, temp;
  box b = getbox();
  for(int i = 0; i < SAMPLESIZE; i++){	
    mpz_set_ui(d_z, d[i]);
    for(int j = 0; j < KEYSIZE; j++){	
      mpz_set_ui(key_hypo_z, key_hypo[j]);
      mpz_xor(v_ij, d_z, key_hypo_z);
      v_ij_t = mpz_get_ui(v_ij);
      temp = b.sbox[v_ij_t];
      v[i][j] = simupower(temp);
    }
  }
  mpz_clears(d_z, key_hypo_z, v_ij,NULL);
}
/* compute correlation */
int computecorrelation(int v[SAMPLESIZE][KEYSIZE], int **trace, double trace_m[KEYSIZE], double v_m[SAMPLESIZE]){	
  double r_ij, left, right, up, down, dvi, dtj, max;
  int k;
  k = 0;
  max = 0;
  left = 0;
  right = 0;
  up = 0;
  down = 0;
	
  for(int i = 0; i < KEYSIZE; i++){	
    for(int j = 0; j < TRACESIZE; j++){	
      for(int d = 0; d < SAMPLESIZE; d++){		
	dvi = v[d][i]- v_m[i];
	dtj = trace[d][j] - trace_m[j];

	up =up + dvi * dtj;
	left =left + pow(dvi, 2);
	right =right +  pow(dtj, 2);
      }

      down = sqrt(left * right);
      r_ij = up / down;

      if(r_ij > max){
	max = r_ij;
	k = i;
      }
      left = 0;
      right = 0;
      up = 0;
      down = 0;
    }		
  }
  return k;
}
/* simulate power, use hamming weight */
int simupower(int v_ij){
  mpz_t zero, v_ij_z;
  mpz_inits(zero, v_ij_z, NULL);
  int ham_w;
  mpz_set_ui(zero, 0);
  mpz_set_ui(v_ij_z, v_ij);
  ham_w = mpz_hamdist(v_ij_z, zero);
  mpz_clears(zero, v_ij_z, NULL);
  return ham_w;
}
/* interact with D */
void interact(char *trace, char *c, char *m){

  fprintf(target_in, "%s\n", m);

  fflush( target_in ); 
  
  fscanf( target_out, "%s", trace );
 
  fscanf( target_out, "%s", c );

}
/* generate samples */
void sampleGen(char m[SAMPLESIZE][SIZE], char c[SAMPLESIZE][SIZE], int **trace){
  char *trace_t, *str, *temp;
  mpz_t m_rand;
  mpz_init(m_rand);

  gmp_randstate_t s;
  gmp_randinit_default(s);
  gmp_randseed_ui(s, time(NULL));

  trace_t = (char*)malloc(sizeof(char)*NUM);

  for(int i = 0; i < SAMPLESIZE; i++){
    temp = trace_t;
    mpz_urandomb (m_rand, s, 128);
    mpz_get_str (m[i], -16, m_rand);           
		
    interact(trace_t, c[i], m[i]);
		
    for(int j = START; j < END; j++){
      if((str = strsep(&temp, ",")) != NULL){
	trace[i][j-START] = atoi(str); 
      }	
    }		
  }
  mpz_clear(m_rand);
}
/* compute trace */
void computetrace(double trace_m[TRACESIZE], int **trace){
  for(int i  = 0; i < TRACESIZE; i++){
    trace_m[i] = 0;
    for(int j = 0; j < SAMPLESIZE; j++){
      trace_m[i] =trace_m[i] + trace[j][i];
    }
    trace_m[i] = trace_m[i] / SAMPLESIZE;
  }
}
/* get the final key */
void getkey(char key[SIZE], char m[SAMPLESIZE][SIZE], int **trace, double trace_m[TRACESIZE]){
  int key_hypo[KEYSIZE], d[SAMPLESIZE];
  int v[SAMPLESIZE][KEYSIZE];
  double v_m[KEYSIZE];
  int k_t;

  for(int i = 0; i < KEYSIZE; i++){
    key_hypo[i]= i;
  }

  for(int i = 0; i < 16; i++){ 			
    // get data
    for(int j = 0; j< SAMPLESIZE; j++){
      char str[3];
      strncpy(str, m[j] + 2*i, 2);
      str[2] = '\0';
      d[j] = (int)strtol(str, NULL, 16);
    }
		
    //get mid vaule 
    computemid(d, key_hypo, v);

    char key_t[2];
    //get vi
    for(int j = 0; j < KEYSIZE; j++){
      v_m[j] = 0;
      for(int k = 0; k <  SAMPLESIZE; k++){
	v_m[j] += v[k][j];
      }
      v_m[j] = v_m[j]/ SAMPLESIZE;
    }
    //get correlation
    k_t = computecorrelation(v, trace, trace_m, v_m); 
    sprintf(key_t, "%02X", k_t);
    printf("%s\n",key_t);
    strncpy(key+2*i, key_t, 2);   
  }
}

void attack(){
  char m[SAMPLESIZE][SIZE], c[SAMPLESIZE][SIZE];
  int **trace;
  double trace_m[TRACESIZE];
  char key[SIZE];
	
  trace=(int **)malloc(sizeof(int*)*SAMPLESIZE);
  for(int i=0;i< SAMPLESIZE;i++){
    trace[i]=(int *)malloc(sizeof(int)*TRACESIZE);
  }
	  
  printf("Generating message...\n");   
  sampleGen(m, c, trace);
	
  printf("Computing trace...\n");
  computetrace(trace_m, trace);
	
  printf("Getting key...\n");   
  getkey(key, m, trace, trace_m);
  
  printf("\nKey:%s\n\n", key);	
	
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

    attack();


    break;
  }
  }
  
  // Clean up any resources we've hung on to.
  cleanup( SIGINT );
  
  return 0;
  
}





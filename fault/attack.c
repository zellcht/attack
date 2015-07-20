#include "attack.h"

#define LENGTH 128
#define SIZE 32

#define BYTES 16
#define SAMPESIZE 10


pid_t pid        = 0;    // process ID (of either parent or child) from fork

int   target_raw[ 2 ];   // unbuffered communication: attacker -> attack target
int   attack_raw[ 2 ];   // unbuffered communication: attack target -> attacker

FILE* target_out = NULL; // buffered attack target input  stream
FILE* target_in  = NULL; // buffered attack target output stream


typedef struct box{
  int sbox[256];
  int sbox_inv[256];
}box;

typedef struct rkey{
  int list[4];
}rkey;

typedef struct keylist{
  int key[2*LENGTH];
  int count;
}keylist;

typedef struct allkeylist{
  keylist key_list[BYTES * SAMPESIZE];
}allkeylist;

void inversekey(int key_final[BYTES], int *s_box, int *hyp_key);
void interact(char *c, char *inject, mpz_t m, int t);
void strtoint(int *int_c, char *str_c, int position);
int deltaN(int x, int x_prime, int k, int *sbox_inv);
void getkeyhypo(int *correct_ct, int *fault_ct, keylist *key_list, int *sbox_inv, int n1, int n2, int n3, int n4);
int checkkey(int key, int *key_list_t, int key_list_size);
box getbox();
void sampleGen(int c_correct[BYTES], int c_fault[BYTES]);
void getkey(int key_hypo[BYTES], allkeylist key_list_all[SAMPESIZE]);
void attack();
/* inverse the key */
void inversekey(int key_final[BYTES], int *s_box, int *hyp_key){
  rkey w[44];
  rkey Rcon[10];
  rkey temp;
  int t;

  Rcon[0].list[0] = 0x01;
  Rcon[1].list[0] = 0x02;
  Rcon[2].list[0] = 0x04;
  Rcon[3].list[0] = 0x08;
  Rcon[4].list[0] = 0x10;
  Rcon[5].list[0] = 0x20;
  Rcon[6].list[0] = 0x40;
  Rcon[7].list[0] = 0x80;
  Rcon[8].list[0] = 0x1B;
  Rcon[9].list[0] = 0x36;

  for (int i = 0; i < 10; i++) {
    Rcon[i].list[1] = 0;
    Rcon[i].list[2] = 0;
    Rcon[i].list[3] = 0;
  }
  for (int i = 0; i < 4; i++) {
    w[40+i].list[0] = hyp_key[4*i];
    w[40+i].list[1] = hyp_key[4*i+1];
    w[40+i].list[2] = hyp_key[4*i+2];
    w[40+i].list[3] = hyp_key[4*i+3];
  }

  for (int i = 40 - 1; i >=0 ; i--) {
    if (i%4 == 0) {
      temp.list[0] = w[i+3].list[0];
      t = temp.list[0];
      for (int j = 1; j < 4; j++) {
	temp.list[j] = w[i+3].list[j];
	temp.list[j-1] = temp.list[j];
      }
      temp.list[3] = t;
      for (int j = 0; j < 4; j++) {
	temp.list[j] = s_box[(temp.list[j])]^(Rcon[i/4].list[j])^(w[i+4].list[j]);
	w[i].list[j] = temp.list[j];
      }
    }
    else{
      for (int j = 0; j < 4; j++) {
	temp.list[j] = (w[i+4].list[j])^(w[i+3].list[j]);
	w[i].list[j] = temp.list[j];
      }
    }
    for (int i = 0; i < 4; i++) {
      key_final[i*4] = w[i].list[0];
      key_final[i*4+1] = w[i].list[1];
      key_final[i*4+2] = w[i].list[2];
      key_final[i*4+3] = w[i].list[3];
    }
  }
}
/* interact with D */
void interact(char *c, char *inject, mpz_t m, int t){
  int correct = 1;
  int fault = 0;
  char *string = NULL;
  string = (char*) malloc(sizeof(char) * 128);
  mpz_get_str(string, -16, m);
  
  if (t == correct) {
    fprintf(target_in, "\n");
  }
  else if (t == fault){
    fprintf(target_in, "%s\n", inject);
  }
  fprintf(target_in, "%s\n", string);

  fflush( target_in ); 
  
  fscanf( target_out, "%s", c );
}
/* convert string to int */
void strtoint(int *int_c, char *str_c, int position){
  char str_c_t[3];
  int length = 2;
  strncpy(str_c_t, (str_c + position), length);
  str_c_t[length] = '\0';
  *int_c = (int)strtol(str_c_t, NULL, 16);
}
/* compute n delta */
int deltaN(int x, int x_prime, int k, int *sbox_inv){
  int r;
  r= (sbox_inv[x^k])^(sbox_inv[x_prime^k]);
  return r;
}
/* compute n x*/
int timeN(int x){
  int t;
  t = x << 1;
  t = (x<<1) ^ (((x>>7) & 1) * 0x11b);
  return t;
}
/* get potential keys */
void getkeyhypo(int *correct_ct, int *fault_ct, keylist *key_list, int *sbox_inv, int n1, int n2, int n3, int n4){
  int delta_n;
  int size = 2 * LENGTH;
  for (int delta = 0; delta < size; delta++) {
    keylist key_1,key_2,key_3,key_4;

    key_1.count = 0;
    key_2.count = 0;
    key_3.count = 0;
    key_4.count = 0;

    /* equation 1 */
    for (int k = 0; k < size; k++) {
      delta_n = deltaN(correct_ct[n1], fault_ct[n1], k, sbox_inv);
      if(delta_n == timeN(delta)){

	key_1.key[key_1.count] = k;
	key_1.count++;
          
      }
    }

    /* equation 2 */
        
    for (int k = 0; k < size; k++) {
      delta_n = deltaN(correct_ct[n2], fault_ct[n2], k, sbox_inv);
      if(delta_n == delta){
	key_2.key[key_2.count] = k;
	key_2.count++;
      }
    }

    /* equation 3 */
        
    for (int k = 0; k < size; k++) {
      delta_n = deltaN(correct_ct[n3], fault_ct[n3], k, sbox_inv);
      if (delta_n == delta){
	key_3.key[key_3.count] = k;
	key_3.count++;
      }
    }

    /* equation 4 */
        
    for (int k = 0; k < size; k++) {
      delta_n = deltaN(correct_ct[n4], fault_ct[n4], k, sbox_inv);
      if(delta_n == (delta^timeN(delta))){
	key_4.key[key_4.count] = k;
	key_4.count++;
      }
    }  

    if (key_1.count > 0 && key_2.count > 0 && key_3.count > 0 && key_4.count > 0){
      for (int i = 0; i < key_1.count; i++) {
	key_list[n1].key[i+key_list[n1].count] = key_1.key[i];
      }
      key_list[n1].count += key_1.count;
            
      for (int i = 0; i < key_2.count; i++) {
	key_list[n2].key[i+key_list[n2].count] = key_2.key[i];
      }
      key_list[n2].count += key_2.count;
            
      for (int i = 0; i < key_3.count; i++) {
	key_list[n3].key[i+key_list[n3].count] = key_3.key[i];
      }
      key_list[n3].count += key_3.count;
            
      for (int i = 0; i < key_4.count; i++) {
	key_list[n4].key[i+key_list[n4].count] = key_4.key[i];
      }
      key_list[n4].count += key_4.count;
    }
  }
    
}
/* check whether the key is in the list or not */
int checkkey(int key, int *key_list_t, int key_list_size){
  for (int i = 0; i < key_list_size; i++) {
    if (key == key_list_t[i]) {
      return 1;
    }
  }
  return 0;
}

/* get S-box and S-box inverse */
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
    },
   
    .sbox_inv =  {
      0x52, 0x09, 0x6A, 0xD5, 0x30, 0x36, 0xA5, 0x38, 0xBF, 0x40, 0xA3, 0x9E, 0x81, 0xF3, 0xD7, 0xFB,
      0x7C, 0xE3, 0x39, 0x82, 0x9B, 0x2F, 0xFF, 0x87, 0x34, 0x8E, 0x43, 0x44, 0xC4, 0xDE, 0xE9, 0xCB,
      0x54, 0x7B, 0x94, 0x32, 0xA6, 0xC2, 0x23, 0x3D, 0xEE, 0x4C, 0x95, 0x0B, 0x42, 0xFA, 0xC3, 0x4E,
      0x08, 0x2E, 0xA1, 0x66, 0x28, 0xD9, 0x24, 0xB2, 0x76, 0x5B, 0xA2, 0x49, 0x6D, 0x8B, 0xD1, 0x25,
      0x72, 0xF8, 0xF6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xD4, 0xA4, 0x5C, 0xCC, 0x5D, 0x65, 0xB6, 0x92,
      0x6C, 0x70, 0x48, 0x50, 0xFD, 0xED, 0xB9, 0xDA, 0x5E, 0x15, 0x46, 0x57, 0xA7, 0x8D, 0x9D, 0x84,
      0x90, 0xD8, 0xAB, 0x00, 0x8C, 0xBC, 0xD3, 0x0A, 0xF7, 0xE4, 0x58, 0x05, 0xB8, 0xB3, 0x45, 0x06,
      0xD0, 0x2C, 0x1E, 0x8F, 0xCA, 0x3F, 0x0F, 0x02, 0xC1, 0xAF, 0xBD, 0x03, 0x01, 0x13, 0x8A, 0x6B,
      0x3A, 0x91, 0x11, 0x41, 0x4F, 0x67, 0xDC, 0xEA, 0x97, 0xF2, 0xCF, 0xCE, 0xF0, 0xB4, 0xE6, 0x73,
      0x96, 0xAC, 0x74, 0x22, 0xE7, 0xAD, 0x35, 0x85, 0xE2, 0xF9, 0x37, 0xE8, 0x1C, 0x75, 0xDF, 0x6E,
      0x47, 0xF1, 0x1A, 0x71, 0x1D, 0x29, 0xC5, 0x89, 0x6F, 0xB7, 0x62, 0x0E, 0xAA, 0x18, 0xBE, 0x1B,
      0xFC, 0x56, 0x3E, 0x4B, 0xC6, 0xD2, 0x79, 0x20, 0x9A, 0xDB, 0xC0, 0xFE, 0x78, 0xCD, 0x5A, 0xF4,
      0x1F, 0xDD, 0xA8, 0x33, 0x88, 0x07, 0xC7, 0x31, 0xB1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xEC, 0x5F,
      0x60, 0x51, 0x7F, 0xA9, 0x19, 0xB5, 0x4A, 0x0D, 0x2D, 0xE5, 0x7A, 0x9F, 0x93, 0xC9, 0x9C, 0xEF,
      0xA0, 0xE0, 0x3B, 0x4D, 0xAE, 0x2A, 0xF5, 0xB0, 0xC8, 0xEB, 0xBB, 0x3C, 0x83, 0x53, 0x99, 0x61,
      0x17, 0x2B, 0x04, 0x7E, 0xBA, 0x77, 0xD6, 0x26, 0xE1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0C, 0x7D
    }
  };
  return b;
}


/* Generate samples */
void sampleGen(int c_correct[BYTES], int c_fault[BYTES]){
  char str_c_correct[SIZE];
  char str_c_fault[SIZE];
  char inject[] = "8,1,0,0,0";

  mpz_t m_rand;
  mpz_init(m_rand);
  gmp_randstate_t s;
  gmp_randinit_default (s);
  gmp_randseed_ui(s,time(NULL));

  int position;
  int correct = 1;
  int fault = 0;

  mpz_urandomb(m_rand, s, LENGTH);
  /* get the correct & fault c */
  interact(str_c_correct, inject, m_rand, correct);
  for (int j = 0; j < BYTES; j++) {
    position = j * 2;
    strtoint(&c_correct[j], str_c_correct, position);
  }
  interact(str_c_fault, inject, m_rand, fault);
  for (int j = 0; j < BYTES; j++) {
    position = j * 2;
    strtoint(&c_fault[j], str_c_fault, position);
  }
  mpz_clear(m_rand);
}
/* get key hypo */
void getkey(int key_hypo[BYTES], allkeylist key_list_all[SAMPESIZE]){
  int count;
  int key;
  int exist;
  int exist_num; 
  int *key_list_t;
  int key_list_size;
  int key_num;
  allkeylist key_list_r;

  for (int i = 0; i < BYTES; i++) {
    key_list_r.key_list[i].count = 0;
  }
  for (int i = 0; i < BYTES; i++) {
    count = key_list_all[0].key_list[i].count;
    for (int j = 0; j < count; j++) {
      exist_num = 0;
      key = key_list_all[0].key_list[i].key[j];
      for (int k = 1; k < SAMPESIZE; k++) {

	key_list_t = key_list_all[k].key_list[i].key;
	key_list_size = key_list_all[k].key_list[i].count;
	exist = checkkey(key, key_list_t, key_list_size);

	if (exist) {
	  exist_num++;
	}
      }
		
      key_num = key_list_r.key_list[i].count;

      if (exist_num == (SAMPESIZE - 1) && !(key_num > 10)) {
	key_list_r.key_list[i].key[key_list_r.key_list[i].count] = key;
	key_list_r.key_list[i].count++;
      }
      if(key_num > 10){
	printf("Too few samples \n");
	exit(1);
      }
    }
  }
  for (int i = 0; i < BYTES; i++) {
    key_num = key_list_r.key_list[i].count;
    if(!(key_num == 1)){
      printf("Sample size too small!\n");
      exit(1);
    }
    else{
      key_hypo[i] = key_list_r.key_list[i].key[0];
    }
  }

}

void attack(){
  int key_hypo[BYTES];
  int key_final[BYTES];
  int c_correct[BYTES];
  int c_fault[BYTES];
  allkeylist key_list_all[SAMPESIZE];
  box box = getbox();

  for (int i = 0; i < SAMPESIZE; i++) {
    for (int j = 0; j < BYTES; j++) {
      key_list_all[i].key_list[j].count = 0;
    }
  }      
  /* get key lists */
  printf("Guessing key bytes...\n");
  for (int i = 0; i < SAMPESIZE; i++) {
    /* Generates m, c, c_fault */
    sampleGen(c_correct, c_fault);
    /* Induce faults */
    getkeyhypo(c_correct, c_fault, key_list_all[i].key_list, box.sbox_inv, 0, 13, 10, 7);
    getkeyhypo(c_correct, c_fault, key_list_all[i].key_list, box.sbox_inv, 11, 4, 1, 14);
    getkeyhypo(c_correct, c_fault, key_list_all[i].key_list, box.sbox_inv, 2, 15, 8, 5);
    getkeyhypo(c_correct, c_fault, key_list_all[i].key_list, box.sbox_inv, 9, 6, 3, 12);
            
  }
  printf("Getting key hypo...\n");
 
  getkey(key_hypo, key_list_all);
  printf("Inversing the key...\n");    
  inversekey(key_final, box.sbox, key_hypo);
        
  printf("\nkey : ");
  for (int i = 0; i < BYTES; i++) {
    printf("%02hhX", key_final[i]);
  }
  printf("\n\n");
        

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





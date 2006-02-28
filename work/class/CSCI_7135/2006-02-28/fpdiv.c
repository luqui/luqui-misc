#include <stdio.h>
#include <papi.h>

#define DATASIZE 10000
#define STRIPSIZE 100
float* data[10000];

#define LOOKAHEAD 30
#define STEPSIZE 20

#ifdef PREFETCH
    #define PFNTA(x) asm("prefetchnta %0" : : "m" (x))
#else
    #define PFNTA(x) asm("nop" : : "m" (x));
#endif

void init()
{
    int i, j;
    for (i = 0; i < DATASIZE; i++) {
        data[i] = (float*)malloc(sizeof(float) * STRIPSIZE);
        for (j = 0; j < STRIPSIZE; j++) {
            data[i][j] = 0.99999;
        }
    }
}

float dodivs()
{
    float accum = 1.0;
    int i, j;
    for (i = 0; i < DATASIZE; i++) {
        for (j = 0; j < STRIPSIZE; j += STEPSIZE) {
            PFNTA(data[i][j+LOOKAHEAD]);
            accum /= data[i][j];
        }
    }
    return accum;
};

float dodivs_concat()
{
    float accum = 1.0;
    int i, j;
    for (i = 0; i < DATASIZE; i++) {
        for (j = 0; j < STRIPSIZE - LOOKAHEAD; j += STEPSIZE) {
            PFNTA(data[i][j + LOOKAHEAD]);
            accum /= data[i][j];
        }

        for (; j < STRIPSIZE; j += STEPSIZE) {
            PFNTA(data[i+1][j - LOOKAHEAD]);
            accum /= data[i][j];
        }
    }
    return accum;
}

int main()
{
  float real_time, proc_time,ipc;
  long_long ins;
  float real_time_i, proc_time_i, ipc_i;
  long_long ins_i;
  int retval;
  float result;

  init();
  
  if((retval=PAPI_ipc(&real_time_i,&proc_time_i,&ins_i,&ipc_i)) < PAPI_OK)
  { 
    printf("Could not initialise PAPI_ipc \n");
    printf("retval: %d\n", retval);
    exit(1);
  }

#ifdef CONCAT
  result = dodivs_concat();
#else
  result = dodivs();
#endif

  if((retval=PAPI_ipc( &real_time, &proc_time, &ins, &ipc))<PAPI_OK)
  {    
    printf("retval: %d\n", retval);
    exit(1);
  }


  printf("Result: %f\n", result);
  printf("Real_time: %f Proc_time: %f Total instructions: %lld IPC: %f\n", 
         real_time, proc_time,ins,ipc);

  /* clean up */
  PAPI_shutdown();
  exit(0);
}

/* This is PAPI_ipc in the examples directory */

#include <stdio.h>
#include "papi.h"

main()
{ 
  float real_time, proc_time,ipc;
  long_long ins;
  float real_time_i, proc_time_i, ipc_i;
  long_long ins_i;
  int retval;

  if((retval=PAPI_ipc(&real_time_i,&proc_time_i,&ins_i,&ipc_i)) < PAPI_OK)
  { 
    printf("Could not initialise PAPI_ipc \n");
    printf("retval: %d\n", retval);
    exit(1);
  }

  my_slow_code();

  
  if((retval=PAPI_ipc( &real_time, &proc_time, &ins, &ipc))<PAPI_OK)
  {    
    printf("retval: %d\n", retval);
    exit(1);
  }


  printf("Real_time: %f Proc_time: %f Total instructions: %lld IPC: %f\n", 
         real_time, proc_time,ins,ipc);

  /* clean up */
  PAPI_shutdown();
  exit(0);
}



volatile int data[2] = { 1 };
volatile float fdata[2] = { 0, 0 };

int my_slow_code()
{
  register int i;
  register int c = 0;
  register int d = 0;

  for(i=1; i<1000000; i++)
  {
      c ^= data[0];
      d += d;
  }
  return d-c;
}


#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>

// interpret 4 bytes read in as x
// if x > 6, write out x-2
// else write out x-1 

unsigned char* readtowrite(unsigned char *inbuf, unsigned char *outbuf) {
  int *ri = (int*)&inbuf[0];
  int x = *ri;
  x--;
  if(x > 5) {
    x--;
  }
  int *wi = (int*)&outbuf[0];
  *wi = x;
  write(1, outbuf, 4);
  return outbuf;
}

int main(int argc, char** argv) {
  unsigned char inbuf[4];
  unsigned char outbuf[4];
  read(0, inbuf, 4);
  readtowrite(inbuf, outbuf);
}

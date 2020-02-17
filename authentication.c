#include <stdio.h>
#include <unistd.h>
void check(char* inbuf) {
    int authreq = (inbuf[0] == 'A' && inbuf[1] == 'U' && inbuf[2] == 'T' && inbuf[3] == 'H');
    int good_password = (inbuf[4] == 'T' && inbuf[5] == 'O' && inbuf[6] == 'D' &&  inbuf[7] == 0);
    if (authreq && !good_password) {
      printf("reject");
    }
}

int main(int argc, char** argv) {
    char inbuf[64];
    int num_bytes;
    num_bytes = read(0, inbuf, 64);
    check(inbuf);
}

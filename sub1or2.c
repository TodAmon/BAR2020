#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>

// return y-1 if y <= 4 else y-2 

int sub1or2(int y) {
  int x = y;
  x--;
  if (x > 5)
    x--;
  return x;
}

int main(int argc, char** argv) {
  printf("foo(%d) = %d\n", 4, sub1or2(4));
  printf("foo(%d) = %d\n", 5, sub1or2(5));
  printf("foo(%d) = %d\n", 6, sub1or2(6));
  printf("foo(%d) = %d\n", 7, sub1or2(7));
  printf("foo(%d) = %d\n", 8, sub1or2(8));
  printf("foo(%d) = %d\n", 9, sub1or2(9));


}

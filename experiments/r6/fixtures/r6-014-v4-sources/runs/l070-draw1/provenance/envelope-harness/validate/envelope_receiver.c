/* Local canned transport, with capture of the bytes actually read at its
   boundary. It does not parse messages, perform inference or use arithmetic.
   The canned response is deliberately independent of the received body. */
#include <stdio.h>
#include <string.h>
#include <unistd.h>

int main(int argc, char **argv) {
  if (argc != 2) return 2;
  FILE *input = fopen("/wire.json", "rb");
  FILE *capture = fopen("/out/received-envelope.json", "wb");
  if (!input || !capture) return 3;
  int ch;
  size_t count = 0;
  while ((ch = fgetc(input)) != EOF) {
    if (++count > 1048576 || fputc(ch, capture) == EOF) return 4;
  }
  if (ferror(input) || fclose(capture)) return 5;
  fclose(input);
  FILE *receipt = fopen("/out/transmission.json", "wb");
  if (!receipt) return 6;
  fprintf(receipt, "{\"completed\":true,\"bytes\":%zu}\n", count);
  if (fclose(receipt)) return 7;
  if (!strcmp(argv[1], "timeout")) { for (;;) pause(); }
  if (!strcmp(argv[1], "transport_error")) return 17;
  if (strcmp(argv[1], "normal")) return 8;
  FILE *response = fopen("/canned.json", "rb");
  if (!response) return 9;
  while ((ch = fgetc(response)) != EOF) if (putchar(ch) == EOF) return 10;
  if (ferror(response) || fflush(stdout)) return 11;
  fclose(response);
  return 0;
}

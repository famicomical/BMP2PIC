CC = gcc
CFLAGS = -O2 -Wall
TARGET = bmp2pic

all: $(TARGET)

$(TARGET): BMP2PIC.C ARIMAC.H
	$(CC) $(CFLAGS) -o $(TARGET) BMP2PIC.C

clean:
	rm -f $(TARGET)

test: $(TARGET)
	./$(TARGET)

.PHONY: all clean test

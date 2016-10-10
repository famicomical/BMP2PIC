// Portable Byte Ordering in C++
// by Philip J. Erdelsky
// Public Domain -- No Restrictions on Use
// Modified/Expanded by Rony Ballouz

// If the byte order of the target machine is known, include ONE of
// the following statements:
//   #define _BIG_ENDIAN
//   #define _LITTLE_ENDIAN

// If the byte order of the target machine is to be determined at run
// time for each conversion, include the following statement:
//   #define _RUN_TIME_ENDIAN

#ifndef _ENDIAN
#define _ENDIAN 1

typedef unsigned char BYTE;
typedef unsigned short WORD; // two-byte word
typedef unsigned int DWORD; // four-byte double word

#ifdef _RUN_TIME_ENDIAN

  extern struct union_endian_union
  {
    DWORD whole;
    WORD half[2];
  } _endian;

  inline int big_endian(void) {return _endian.half[1];}
  inline int little_endian(void) {return _endian.half[0];}

#endif

// check for consistent parameter definitions

#ifdef _BIG_ENDIAN
  #ifdef _LITTLE_ENDIAN
    #error _BIG_ENDIAN and _LITTLE_ENDIAN both defined
  #endif
  #ifdef _RUN_TIME_ENDIAN
    #error _BIG_ENDIAN and RUN_TIME_ENDIAN both defined
  #endif
#endif

#ifdef _LITTLE_ENDIAN
  #ifdef _RUN_TIME_ENDIAN
    #error _LITTLE_END1AN and _RUN_TIME_ENDIAN both defined
  #endif
#endif

class BEWORD  // big endian WORD
{
   union
   {
     BYTE half[2];
     WORD whole;
   } x;
 public:
   void set(WORD n)
   {
     #ifdef _BIG_ENDIAN
       x.whole = n;
       *((WORD*)x.half)=n;
     #else
       #ifdef _RUN_TIME_ENDIAN
         if (big_endian()) {
         	x.whole = n;
	       *((WORD*)x.half)=n;	
         }
         else {
       #endif
       x.half[0] = n >> 8;
       x.half[1] = n;
       x.whole = *((WORD*)(x.half));
       #ifdef _RUN_TIME_ENDIAN
         }
       #endif
     #endif
   }
   BEWORD(WORD n) {set(n);}
   WORD val(void)
   {
     return
       #ifdef _BIG_ENDIAN
         x.whole
       #else
         #ifdef RUN_TIME_ENDIAN
         big_endian() ? x.whole :
       #endif
       x.half[0] << 8 | x.half[1]
     #endif
       ;
   }
   DWORD whole(void){
   	return x.whole;
   }
   int zero(void) {return x.whole == 0;}
   int nonzero(void) {return x.whole != 0;}
   int operator == (BEWORD &n) {return x.whole == n.x.whole;}
   int operator != (BEWORD &n) {return x.whole != n.x.whole;}
};

class BEDWORD  // big endian DWORD
{
   union
   {
     BYTE quarter[4];
     DWORD whole;
   } x;
 public:
   void set(DWORD n)
   {
     #ifdef _BIG_ENDIAN
       x.whole = n;
       *((DWORD*)x.quarter)=n;
     #else
       #ifdef _RUN_TIME_ENDIAN
         if (big_endian()) {
         	x.whole = n;
         	*((DWORD*)x.quarter)=n;
         }
         else{
       #endif
       x.quarter[0] = n >> 24;
       x.quarter[1] = n >> 16;
       x.quarter[2] = n >> 8;
       x.quarter[3] = n;
       x.whole = *((DWORD*)(x.quarter));
       #ifdef _RUN_TIME_ENDIAN
         }
       #endif
     #endif
   }
   BEDWORD(DWORD n) {set(n);}
   DWORD val(void)
   {
     return
       #ifdef _BIG_ENDIAN
         x.whole
     #else
       #ifdef _RUN_TIME_ENDIAN
         big_endian() ? x.whole:
       #endif
       (DWORD) x.quarter[0] << 24 | (DWORD) x.quarter[1] << 16 |
          x.quarter[2] << 8 | x.quarter[3];
     #endif
       ;
   }
   DWORD whole(void){
   	return x.whole;
   }
   int zero(void) {return x.whole == 0;}
   int nonzero(void) {return x.whole != 0;}
   int operator == (BEDWORD &n) {return x.whole == n.x.whole;}
   int operator != (BEDWORD &n) {return x.whole != n.x.whole;}
};

class LEWORD  // little endian WORD
{
   union
   {
     BYTE half[2];
     WORD whole;
   } x;
 public:
   void set(WORD n)
   {
     #ifdef _LITTLE_ENDIAN
       x.whole = n;
       *((WORD*)x.half)=n;
     #else
       #ifdef _RUN_TIME_ENDIAN
         if (little_endian()){
         	x.whole = n;
         	*((WORD*)x.half)=n;
         }
         else {
       #endif
       x.half[1] = n >> 8;
       x.half[0] = n;
       x.whole = *((WORD*)(x.half));
       #ifdef _RUN_TIME_ENDIAN
         }
       #endif
     #endif
   }
   LEWORD(WORD n) {set(n);}
   WORD val(void)
   {
     return
       #ifdef _LITTLE_ENDIAN
         x.whole
       #else
         #ifdef _RUN_TIME_ENDIAN
           little_endian() ? x.whole :
         #endif
         x.half[1] << 8 | x.half[0]
       #endif
         ;
   }
   DWORD whole(void){
   	return x.whole;
   }
   int zero(void) {return x.whole == 0;}
   int nonzero(void) {return x.whole != 0;}
   int operator == (LEWORD &n) {return x.whole == n.x.whole;}
   int operator != (LEWORD &n) {return x.whole != n.x.whole;}
};

class LEDWORD  // little endian DWORD
{
   union
   {
     BYTE quarter[4];
     DWORD whole;
   } x;
 public:
   void set(DWORD n)
   {
     #ifdef _LITTLE_ENDIAN
       x.whole = n;
       *((DWORD*)x.quarter)=n;
     #else
       #ifdef _RUN_TIME_ENDIAN
         if (little_endian()){
          x.whole = n;
          *((DWORD*)x.quarter)=n;
      	 }
         else {
       #endif
       x.quarter[0] = n;
       x.quarter[1] = n >> 8;
       x.quarter[2] = n >> 16;
       x.quarter[3] = n >> 24;
       x.whole = *((DWORD*)(x.quarter));
       #ifdef _RUN_TIME_ENDIAN
         }
       #endif
     #endif
   }
   LEDWORD(DWORD n) {set(n);}
   DWORD val(void)
   {
     return
       #ifdef _LITTLE_ENDIAN
         x.whole
       #else
         #ifdef _RUN_TIME_ENDIAN
           little_endian() ? x.whole :
         #endif
         x.quarter[0] | x.quarter[1] << 8 |
           (DWORD) x.quarter[2] << 16 | (DWORD) x.quarter[3] << 24;
       #endif
         ;
   }
   DWORD whole(void){
   	return x.whole;
   }
   int zero(void) {return x.whole == 0;}
   int nonzero(void) {return x.whole != 0;}
   int operator == (LEDWORD &n) {return x.whole == n.x.whole;}
   int operator != (LEDWORD &n) {return x.whole != n.x.whole;}
};

//! Byte swap unsigned short
ushort swap_ushort( ushort val ) 
{
    return (val << 8) | (val >> 8 );
}

//! Byte swap short
short swap_short( short val ) 
{
    return (val << 8) | ((val >> 8) & 0xFF);
}

//! Byte swap unsigned int
uint swap_uint( uint val )
{
    val = ((val << 8) & 0xFF00FF00 ) | ((val >> 8) & 0xFF00FF ); 
    return (val << 16) | (val >> 16);
}

//! Byte swap int
int swap_int( int val )
{
    val = ((val << 8) & 0xFF00FF00) | ((val >> 8) & 0xFF00FF ); 
    return (val << 16) | ((val >> 16) & 0xFFFF);
}

#endif
/* End of File */

/* ----------------------------------------------------------------- */

typedef unsigned char  uchar ;
typedef unsigned short ushort ;
typedef unsigned int  ulongg ;

#define numberof(x)	( sizeof ( x ) / sizeof ( * ( x ) ) )
#define alloca(x)	__builtin_alloca ( x )

#define	S_IREAD		0		/*“Ç‚Ýž‚Ýê—p				*/
#define	S_IWRITE	1		/*‘‚«ž‚Ý‰Â”\				*/
#define	S_IFDIR		16		/*ƒfƒBƒŒƒNƒgƒŠ[			*/
#define	S_IFREG		32		/*’Êí					*/
#define	S_IEXEC		64		/*ŽÀs					*/
#define	S_IFCHR		128		/*ƒfƒoƒCƒX				*/


/* ----------------------------------------------------------------- */

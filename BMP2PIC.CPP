/* ----------------------------------------------------------------- *
* PROGRAM-ID.	BMP2PIC.C					     *
* AUTHOR.	ARIMAC.						     *
* DATE-WRITTEN.	1994.05.30					     *
* REMARKS.							     *
*								     *
*　・MS-Windows の BMP ファイルを PIC ファイルに変換する。	     *
*　・ただし、２／１６／２５６／１６７８万色非圧縮のファイルのみ	     *
*　　対応。							     *
*								     *
* HISTORY.							     *
*								     *
*　 1994.05.30	v0.01 誕生					     *
*								     *
*　 1994.08.23	v0.02 出力先ディレクトリを指定出来るようにした。     *
*		      512ライン超え分割画像のエッジマップの初期化を  *
*		      忘れていた。				     *
*								     *
*　 1994.09.21	v0.03 エラーになったファイルは無視するようにした。   *
*		      変換中のラインが分かるようにした。	     *
*		      ２色画像の変化点の探査を失敗してた(^^;	     *
*		      高速化。					     *
*								     *
* ----------------------------------------------------------------- */

#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
#include <string.h>
#include <setjmp.h>
#define _LITTLE_ENDIAN 1    //Modern computers are usually little endian
#include "ENDIAN.H"
typedef unsigned char  uchar ;
typedef unsigned short ushort ;
typedef unsigned int  ulongg ;

#define numberof(x) ( sizeof ( x ) / sizeof ( * ( x ) ) )

#pragma pack(push, 1)

/* ---------------------------------------------------------------- */

#define mbsizeof(TYPE,MEMBER)	(sizeof(((TYPE *)0)->MEMBER))
#define swap_parm(TYPE,MEMBER)	offsetof(TYPE,MEMBER),mbsizeof(TYPE,MEMBER)

/* ---------------------------------------------------------------- */

typedef ushort PIXEL ;
#define RGB(wr,wg,wb)	((PIXEL)(((((wg)<<5|(wr))<<5|(wb))<<1)+1))

/* ---------------------------------------------------------------- */

typedef struct {
  ushort bfType ;
  ulongg  bfSize ;
  ushort bfReserved1 ;
  ushort bfReserved2 ;
  ulongg  bfOffBits ;
} BITMAP_FILE_HEADER ;

static char bmp_fil_hdr_swap [ ] = {
  swap_parm ( BITMAP_FILE_HEADER , bfSize    ) ,
  swap_parm ( BITMAP_FILE_HEADER , bfOffBits ) ,
} ;

/* ---------------------------------------------------------------- */

typedef struct {
  ulongg  biSize ;
  ulongg  biWidth ;
  ulongg  biHeight ;
  ushort biPlanes ;
  ushort biBitCount ;
  ulongg  biCompression ;
  ulongg  biSizeImage ;
  ulongg  biXPelsPerMeter ;
  ulongg  biYPelsPerMeter ;
  ulongg  biClrUsed ;
  ulongg  biClrImportant ;
} BITMAP_INFO_HEADER ;

static char bmp_inf_hdr_swap [ ] = {
  swap_parm ( BITMAP_INFO_HEADER , biSize          ) ,
  swap_parm ( BITMAP_INFO_HEADER , biWidth         ) ,
  swap_parm ( BITMAP_INFO_HEADER , biHeight        ) ,
  swap_parm ( BITMAP_INFO_HEADER , biPlanes        ) ,
  swap_parm ( BITMAP_INFO_HEADER , biBitCount      ) ,
  swap_parm ( BITMAP_INFO_HEADER , biCompression   ) ,
  swap_parm ( BITMAP_INFO_HEADER , biSizeImage     ) ,
  swap_parm ( BITMAP_INFO_HEADER , biXPelsPerMeter ) ,
  swap_parm ( BITMAP_INFO_HEADER , biYPelsPerMeter ) ,
  swap_parm ( BITMAP_INFO_HEADER , biClrUsed  	   ) ,
  swap_parm ( BITMAP_INFO_HEADER , biClrImportant  ) ,
} ;

/* ---------------------------------------------------------------- */

typedef struct {
  char rgbBlue ;
  char rgbGreen ;
  char rgbRed ;
  char rgbReserved ;
} RGB_QUAD ;

/* ---------------------------------------------------------------- */

static struct CL_CACHE {
  PIXEL color ;
  char next ;
  char prev ;
} cl_cache [ 128 ] ;

static int cur_cl_ix ;

/* ---------------------------------------------------------------- */

static int x_arg_chk ( int argc , char * argv [ ] ) ;
static void x_print_help ( int argc , char * argv [ ] ) ;
static int x_file_proc ( char * fname_pt1 ) ;

static int x_bmp_pic_conv ( char * fname_pt1 , int dir_len1 ) ;
static void x_swap_bytes ( void * buf_pt1 , char * ctl_pt1 , int cnt1 ) ;

static int x_bmp_pic_conv1 ( void ) ;
static int x_bmp_pic_conv4 ( void ) ;
static int x_bmp_pic_conv8 ( void ) ;
static int x_bmp_pic_conv24 ( void ) ;

static void x_write_hdr ( int cl_bit1 ) ;
static void str_write ( void * str_pt1 ) ;
static void x_conv_palette ( int cl_bit1 ) ;
static void x_read_bmp_image8 ( int oy1 , int syl1 ) ;

static void x_mark_diff_point1 ( int oy1 , int syl1 ) ;
static void x_compress1 ( int oy1 , int syl1 ) ;

static void x_compress_chain1 ( int sx1 , int sy1 ,
    char * edge_map_pt1 , char * img_buf_pt1 ,  char cl1 ) ;

static void x_mark_diff_point4 ( int oy1 , int syl1 ) ;
static void x_compress4 ( int oy1 , int syl1 ) ;

static void x_compress_chain4 ( int sx1 , int sy1 ,
    char * edge_map_pt1 , char * img_buf_pt1 , char cl1 ) ;

static void x_mark_diff_point8 ( int oy1 , int syl1 ) ;
static void x_compress8 ( int oy1 , int syl1 ) ;

static void x_compress_chain8 ( int sx1 , int sy1 ,
    char * edge_map_pt1 , char * img_buf_pt1 , char cl1 ) ;

static void x_read_bmp_image24 ( int oy1 , int syl1 ) ;
static void mk_cnvtbl ( void ) ;
static void x_conv_line24 ( PIXEL * img_pt1 , char * bmp_pt1 , int sxl1 ) ;
static void x_init_color_cash ( void ) ;
static void x_mark_diff_point16 ( int oy1 , int syl1 ) ;
static void x_compress15 ( int oy1 , int syl1 ) ;

static void x_compress_chain15 ( int sx1 , int sy1 ,
    char * edge_map_pt1 , PIXEL * img_buf_pt1 , PIXEL cl1 ) ;

static void write_len ( int n ) ;
static void write_color15 ( PIXEL cl1 ) ;
static int search_col ( PIXEL cl1 ) ;
static void set_color ( int ix1 ) ;
static void bit_write ( int wlen1 , ulongg wdata1 ) ;
static void x_flush_buff ( void ) ;
static ulongg swap_ulongg(ulongg bigend);
static ushort swap_ushort(ushort bigend);
static short swap_short(short bigend);
static int swap_int(int bigend);

/* ---------------------------------------------------------------- */

static char dos_mode = 0 ;		/* 1:パスの区切りを￥に変換する。 */
static char info_mode = 0 ;		/* 1:情報表示モード */
static char * out_dir1 = NULL ;	/* 出力先指定 */
static char trans_mode = 0 ;		/* 1:拡張子 .BMP を付けない。 */
static char verbose_mode = 0 ;		/* 1:お喋りモード */

static char * bmp_fname_pt1 ;
static int bmp_fh ;
static FILE* bmp_f;
static int bmp_file_date1 = 0 ;	/* BMPファイル日付 */

static BITMAP_FILE_HEADER bmp_fil_hdr ;
static BITMAP_INFO_HEADER bmp_inf_hdr ;

static int buf_xb1 , buf_yl1 ;
static int edge_xb1 ;
static ulongg edge_sz1 ;

static char * pic_fname_pt1 ;
static int pic_fh ;
static FILE* pic_f;
static int bit_len ;
static int buff_len ;
static ulongg pic_bit_data ;
static ulongg * pic_put_pt ;
static ulongg pic_buf [ 2048 ] ;

static jmp_buf wenv1 ;

static char * edge_map1 ;	/* ２色は big endian、その他は little endian */
static char * img_buf8 ;
static PIXEL * img_buf16 ;

static PIXEL red_cnv_tbl   [ 256 ] ;
static PIXEL green_cnv_tbl [ 256 ] ;
static PIXEL blue_cnv_tbl  [ 256 ] ;

/* ---------------------------------------------------------------- */

#define x_strlen(s)	strlen ( ( char * ) ( s ) )
#define x_strcpy(d,s)	strcpy ( ( char * ) ( d ) , ( char * ) ( s ) )

/* ---------------------------------------------------------------- */

int main ( int argc , char * argv [ ] )
{
  int retc , ix1 , fcnt1 ;
  char wch1 ;
  char * ch_pt1 ;

  puts ( "X68k BMP2PIC v0.03 Copyright 1994 Arimac" ) ;
  puts ( "BMP to PIC File Converter (2/16/256/16M Colors)" ) ;
  puts ( "cshwild (By Mad Player) included" ) ;

  if ( x_arg_chk ( argc , argv ) != 0 ) goto lb600 ;

  fcnt1 = 0 ;

  for ( ix1 = 1 ; ix1 < argc ; ix1 ++ ) {
    ch_pt1 = argv [ ix1 ] ;
    wch1 = * ch_pt1 ;
    if ( wch1 == '-' || wch1 == '/' ) {
      if ( ch_pt1 [ 1 ] == 0 ) {
        if ( ++ ix1 >= argc ) goto lb600 ;
        if ( x_file_proc ( argv [ ix1 ] ) < 0 ) goto lb800 ;
        fcnt1 ++ ;
      }
     } else {
      if ( x_file_proc ( ch_pt1 ) < 0 ) goto lb800 ;
      fcnt1 ++ ;
    }
  }

  if ( fcnt1 <= 0 ) goto lb600 ;
  exit ( EXIT_SUCCESS ) ;

lb600 :
  x_print_help ( argc , argv ) ;

lb800 :
  exit ( EXIT_FAILURE ) ;
}

/* ---------------------------------------------------------------- */

static int x_arg_chk ( int argc , char * argv [ ] )
{
  int ix1 , wk1 ;
  char wch1 ;
  char * ch_pt1 ;

  for ( ix1 = 1 ; ix1 < argc ; ix1 ++ ) {
    ch_pt1 = argv [ ix1 ] ;
    wch1 = * ch_pt1 ++ ;
    if ( wch1 == '-' || wch1 == '/' ) {
      switch ( * ch_pt1 ++ ) {
      case 'd' : case 'D' : dos_mode = 1 ;		break ;
      case 'i' : case 'I' : info_mode = 1 ;		break ;
      case 'o' : case 'O' : out_dir1 = ch_pt1 ;		break ;
      case 't' : case 'T' : trans_mode = 1 ;		break ;
      case 'v' : case 'V' : verbose_mode = 1 ;		break ;
      case 0 :
        if ( ++ ix1 >= argc ) goto lb800 ;
        break ;
      default :
        goto lb800 ;
      }
    }
  }

  return ( 0 ) ;

lb800 :
  return ( - 1 ) ;
}

/* ---------------------------------------------------------------- */

static void x_print_help ( int argc , char * argv [ ] )
{
  int wlen1 ;
  char * ch_pt1 , * ch_pt2 ;

  if ( argc > 0 ) {
    ch_pt1 = argv [ 0 ] ;
    if ( ( ch_pt2 = strrchr ( ch_pt1 , (char)'/' ) ) == NULL ) {
      ch_pt2 = ch_pt1 ;
     } else {
      ch_pt2 ++ ;
    }
    if ( ( ch_pt1 = strrchr ( ch_pt2 , '.' ) ) != NULL ) {
      wlen1 = ch_pt1 - ch_pt2 ;
      ch_pt1 = (char*) alloca ( wlen1 + 1 ) ;
      memcpy ( ch_pt1 , ch_pt2 , wlen1 ) ;
      ch_pt1 [ wlen1 ] = 0 ;
      ch_pt2 = ch_pt1 ;
    }
   } else {
    ch_pt2 = "BMP2PIC" ;
  }

  printf ( "使用法：%s［スイッチ］…［ファイル名[.BMP]］…\n" , ch_pt2 ) ;
  puts ( "\t-d\t\tパスの区切りを\\に変換する" ) ;
  puts ( "\t-i\t\tファイル情報表示" ) ;
  puts ( "\t-o出力先\t出力先ディレクトリ指定" ) ;
  puts ( "\t-t\t\t拡張子 .BMP を付けない" ) ;
  puts ( "\t-v\t\tお喋りモード" ) ;
  puts ( "\t※変換結果は拡張子を .PIC にして出力。" ) ;
}

/* ---------------------------------------------------------------- */

static int x_file_proc ( char * path_pt1 )
{
  char * fname_pt1 , * path_pt2 , * path_pt3 , * ch_pt1 ;

  fname_pt1 = path_pt1 ;
  if ( ( ch_pt1 = strrchr ( fname_pt1 , '/'  ) ) != NULL ) fname_pt1 = ch_pt1 + 1 ;
  if ( ( ch_pt1 = strrchr ( fname_pt1 , '\\' ) ) != NULL ) fname_pt1 = ch_pt1 + 1 ;
  if ( ( ch_pt1 = strrchr ( fname_pt1 , ':'  ) ) != NULL ) fname_pt1 = ch_pt1 + 1 ;

  if ( trans_mode == 0 && strchr ( fname_pt1 , '.' ) == NULL ) {
    path_pt2 = (char*) alloca (  x_strlen ( path_pt1 ) + 5 ) ;
    sprintf (  path_pt2 , "%s.BMP" , path_pt1 ) ;
   } else {
    path_pt2 = path_pt1 ;
  }

  if ( dos_mode != 0 ) {
    path_pt3 = (char*) alloca ( x_strlen ( path_pt2 ) + 1 ) ;
    x_strcpy ( path_pt3 , path_pt2 ) ;
    ch_pt1 = path_pt3 ;
    while ( ( ch_pt1 = strchr ( ch_pt1 , '/' ) ) != NULL ) * ch_pt1 ++ = '\\' ;
    path_pt2 = path_pt3 ;
  }

  return ( x_bmp_pic_conv ( path_pt2 , fname_pt1 - path_pt1 ) ) ;
}

/* ---------------------------------------------------------------- */

static int x_bmp_pic_conv ( char * path_pt1 , int dir_len1 )
{
  int bmp_openf , pic_openf ;
  int wlen1 , wlen2 , retc ;
  char wch1 ;
  char * ch_pt1 , * path_pt2 ;
  int ( * proc_pt1 ) ( ) ;

  bmp_openf = pic_openf = 0 ;
  bmp_fname_pt1 = path_pt2 = path_pt1 ;

  if ( out_dir1 != NULL ) {
    wlen1 = x_strlen ( out_dir1 ) ;
    wlen2 = x_strlen ( path_pt1 + dir_len1 ) ;
    path_pt2 = (char *) alloca ( wlen1 + wlen2 + 2 ) ;
    if ( wlen1 > 0 ) {
      memcpy ( path_pt2 , out_dir1 , wlen1 ) ;
      wch1 = out_dir1 [ wlen1 - 1 ] ;
      if ( wch1 != ':' && wch1 != '\\' && wch1 != '/' ) {
        if ( dos_mode == 0 ) {
          wch1 = '/' ;
         } else {
          wch1 = '\\' ;
        }
        path_pt2 [ wlen1 ++ ] = wch1 ;
      }
    }
    memcpy ( path_pt2 + wlen1 , path_pt1 + dir_len1 , wlen2 + 1 ) ;
  }

  if ( ( ch_pt1 = strrchr ( path_pt2 + dir_len1 , '.' ) ) == NULL ) {
    wlen1 = x_strlen ( path_pt2 ) ;
   } else {
    wlen1 = ch_pt1 - path_pt2 ;
  }

  pic_fname_pt1 = (char*) alloca ( wlen1 + 5 ) ;
  memcpy ( pic_fname_pt1 , path_pt2 , wlen1 ) ;
  x_strcpy ( pic_fname_pt1 + wlen1 , ".PIC" ) ;

  if ( ( bmp_fh = fileno(fopen (  path_pt1 , "rb" ))) < 0 ) {

    printf ( "%s はオープン出来ません。\n" , path_pt1 ) ;
    goto lb720 ;
  }
  bmp_openf = 1 ;
  bmp_f = fopen(path_pt1, "rb");
 // bmp_file_date1 = getft ( bmp_fh ) ;

  if ( fread (  & bmp_fil_hdr , 1,sizeof ( bmp_fil_hdr ), bmp_f ) !=
                                       sizeof ( bmp_fil_hdr ) ) goto lb700 ;

  // x_swap_bytes ( & bmp_fil_hdr , bmp_fil_hdr_swap , numberof ( bmp_fil_hdr_swap ) / 2 ) ;

  if ( info_mode != 0 ) {
    printf ( "FileName ･････････ %s\n"         , path_pt1 ) ;
    printf ( "FileType ･････････ %04X\n"       , bmp_fil_hdr . bfType ) ;
    printf ( "FileSize ･････････ %d [bytes]\n" , bmp_fil_hdr . bfSize ) ;
    printf ( "bfOffBits ････････ %d\n"         , bmp_fil_hdr . bfOffBits ) ;
  }

  if ( bmp_fil_hdr . bfType != 19778 ) goto lb700 ;

  if ( (fread ( & bmp_inf_hdr , 1, sizeof ( bmp_inf_hdr ), bmp_f) ) !=
                                       sizeof ( bmp_inf_hdr ) ) goto lb700 ;

  // x_swap_bytes ( & bmp_inf_hdr , bmp_inf_hdr_swap , numberof ( bmp_inf_hdr_swap ) / 2 ) ;

  if ( info_mode == 0 ) {
    printf ( "convert %s (%d bit, %d x %d) to %s\n" ,
        path_pt1 , bmp_inf_hdr . biBitCount ,
        bmp_inf_hdr . biWidth , bmp_inf_hdr . biHeight , pic_fname_pt1 ) ;
   } else {
    printf ( "biSize ･･･････････ %d [bytes]\n"        , bmp_inf_hdr . biSize ) ;
    printf ( "biWidth ･･････････ %d [pixels]\n"       , bmp_inf_hdr . biWidth ) ;
    printf ( "biHeight ･････････ %d [pixels]\n"       , bmp_inf_hdr . biHeight ) ;
    printf ( "biPlanes ･････････ %d\n"                , bmp_inf_hdr . biPlanes ) ;
    printf ( "biBitCount ･･･････ %d [bits]\n"         , bmp_inf_hdr . biBitCount ) ;
    printf ( "biCompression ････ %d\n"                , bmp_inf_hdr . biCompression ) ;
    printf ( "biSizeImage ･･････ %d [bytes]\n"        , bmp_inf_hdr . biSizeImage ) ;
    printf ( "biXPelsPerMeter ･･ %d [pixels/meter]\n" , bmp_inf_hdr . biXPelsPerMeter ) ;
    printf ( "biYPelsPerMeter ･･ %d [pixels/meter]\n" , bmp_inf_hdr . biYPelsPerMeter ) ;
    printf ( "biClrUsed ････････ %d [colors]\n"       , bmp_inf_hdr . biClrUsed ) ;
    printf ( "biClrImportant ･･･ %d [colors]\n\n"     , bmp_inf_hdr . biClrImportant ) ;
    goto lb500 ;
  }

  if ( bmp_inf_hdr . biCompression != 0 ) {
    printf ( "%s は圧縮されているので対応できません。\n" , path_pt1 ) ;
    goto lb720 ;
  }

  switch ( bmp_inf_hdr . biBitCount ) {
  case  1 : proc_pt1 = x_bmp_pic_conv1 ;	break ;		/* 2色 */
  case  4 : proc_pt1 = x_bmp_pic_conv4 ;	break ;		/* 16色 */
  case  8 : proc_pt1 = x_bmp_pic_conv8 ;	break ;		/* 256色 */
  case 24 : proc_pt1 = x_bmp_pic_conv24 ;	break ;		/* 1678色 */
  default :
    printf ( "%s は2色、16色、256色又は1678万色データではありません。\n" ,
             path_pt1 ) ;
    goto lb720 ;
  }

  if ( ( pic_fh = fileno(fopen ( pic_fname_pt1 , "wb") )) < 0 ) {

    printf ( "%s が作成出来ません。\n" , pic_fname_pt1 ) ;
    goto lb800 ;
  }
  pic_openf = 1 ;
  pic_f = fopen(pic_fname_pt1, "wb");


  pic_put_pt = pic_buf ;
  buff_len = numberof ( pic_buf ) ;
  bit_len = sizeof ( pic_bit_data ) * 8 ;

  if ( ( * proc_pt1 ) ( ) != 0 ) goto lb800 ;

  x_flush_buff ( ) ;
 // chgft ( pic_fh , bmp_file_date1 ) ; // used for transferring timestamp from bmp to pic

  pic_openf = 0 ;
  if ( fclose ( pic_f ) < 0 ) {
    printf ( "%s が作成出来ません。\n" , pic_fname_pt1 ) ;
    goto lb800 ;
  }

  bmp_openf = 0 ;
  fclose ( bmp_f) ;

lb500 :
  retc = 0 ;
  goto lb900 ;

lb700 :
  printf ( "%s は BMP ファイルではありません。\n" , path_pt1 ) ;

lb720 :
  retc = 1 ;
  goto lb900 ;

lb800 :
  retc = - 1 ;

lb900 :
  if ( pic_openf != 0 ) fclose ( pic_f ) ;
  if ( bmp_openf != 0 ) fclose ( bmp_f ) ;
  return ( retc ) ;
}

/* ---------------------------------------------------------------- */

static void x_swap_bytes ( void * buf_pt1 , char * ctl_pt1 , int cnt1 )
{
  int cnt2 ;
  char wch1 ;
  char * ch_pt1 , * ch_pt2 ;

  while ( cnt1 -- ) {
    ch_pt1 = ( char * ) buf_pt1 + * ctl_pt1 ++ ;
    cnt2 = * ctl_pt1 ++ ;
    ch_pt2 = ch_pt1 + cnt2 ;
    cnt2 >>= 1 ;
    while ( cnt2 -- ) {
      wch1 = * ch_pt1 ;
      * ch_pt1 ++ = * -- ch_pt2 ;
      * ch_pt2 = wch1 ;
    }
  }
}

/* ---------------------------------------------------------------- */

static int x_bmp_pic_conv1 ( void )
{
  int big_img_sw1 , oy1 , syl1 ;
  ulongg img_xl1 , img_yl1 ;
  ulongg buf_sz1 ;

  edge_map1 = NULL ;
  img_buf8 = NULL ;
  big_img_sw1 = 0 ;

  if ( setjmp ( wenv1 ) != 0 ) goto lb800 ;

  x_write_hdr ( 4 ) ;
  x_conv_palette ( 4 ) ;

  img_xl1 = bmp_inf_hdr . biWidth ;
  img_yl1 = bmp_inf_hdr . biHeight ;

  buf_xb1 = ( ( img_xl1 + 7 ) / 8 + 3 ) & ~ 3 ;		/* BMP line width */
  buf_yl1 = img_yl1 ;

  if ( img_xl1 * img_yl1 > 1024 * 512 && img_yl1 > 512 ) {
    buf_yl1 = 512 ;
    big_img_sw1 = 1 ;
  }

  buf_sz1 = buf_xb1 * buf_yl1 ;
  edge_xb1 = ( img_xl1 + 7 ) >> 3 ;
  edge_sz1 = edge_xb1 * buf_yl1 ;

  if ( ( edge_map1 = malloc ( edge_sz1 ) ) == NULL ) {
    puts ( "edge_map can't alloc" ) ;
    goto lb800 ;
  }

  if ( ( img_buf8 = malloc ( buf_sz1 ) ) == NULL ) {
    puts ( "img_buf can't alloc" ) ;
    goto lb800 ;
  }

  if ( big_img_sw1 == 0 ) {
    x_read_bmp_image8 ( 0 , img_yl1 ) ;
    x_mark_diff_point1 ( 0 , img_yl1 ) ;
    x_compress1 ( 0 , img_yl1 ) ;
   } else {
    for ( oy1 = 0 ; oy1 + 512 < img_yl1 ; oy1 += 512 ) {
      x_read_bmp_image8 ( oy1 , 512 ) ;
      x_mark_diff_point1 ( oy1 , 512 ) ;
      x_compress1 ( oy1 , 512 ) ;
    }

    syl1 = img_yl1 - oy1 ;
    x_read_bmp_image8 ( oy1 , syl1 ) ;
    x_mark_diff_point1 ( oy1 , syl1 ) ;
    x_compress1 ( oy1 , syl1 ) ;
  }

  if ( verbose_mode != 0 ) printf ( "\n" ) ;
  free ( img_buf8 ) ;
  img_buf8 = NULL ;
  free ( edge_map1 ) ;
  edge_map1 = NULL ;
  return ( 0 ) ;

lb800 :
  if ( img_buf8  != NULL ) free ( img_buf8  ) ;
  if ( edge_map1 != NULL ) free ( edge_map1 ) ;
  return ( - 1 ) ;
}

/* ---------------------------------------------------------------- */

static int x_bmp_pic_conv4 ( void )
{
  int big_img_sw1 , oy1 , syl1 ;
  ulongg img_xl1 , img_yl1 ;
  ulongg buf_sz1 ;

  edge_map1 = NULL ;
  img_buf8 = NULL ;
  big_img_sw1 = 0 ;

  if ( setjmp ( wenv1 ) != 0 ) goto lb800 ;

  x_write_hdr ( 4 ) ;
  x_conv_palette ( 4 ) ;

  img_xl1 = bmp_inf_hdr . biWidth ;
  img_yl1 = bmp_inf_hdr . biHeight ;

  buf_xb1 = ( ( img_xl1 + 1 ) / 2 + 3 ) & ~ 3 ;		/* BMP line width */
  buf_yl1 = img_yl1 ;

  if ( img_xl1 * img_yl1 > 1024 * 512 && img_yl1 > 512 ) {
    buf_yl1 = 512 ;
    big_img_sw1 = 1 ;
  }

  buf_sz1 = buf_xb1 * buf_yl1 ;
  edge_xb1 = ( img_xl1 + 7 ) >> 3 ;
  edge_sz1 = edge_xb1 * buf_yl1 ;

  if ( ( edge_map1 = malloc ( edge_sz1 ) ) == NULL ) {
    puts ( "edge_map can't alloc" ) ;
    goto lb800 ;
  }

  if ( ( img_buf8 = malloc ( buf_sz1 ) ) == NULL ) {
    puts ( "img_buf can't alloc" ) ;
    goto lb800 ;
  }

  if ( big_img_sw1 == 0 ) {
    x_read_bmp_image8 ( 0 , img_yl1 ) ;
    x_mark_diff_point4 ( 0 , img_yl1 ) ;
    x_compress4 ( 0 , img_yl1 ) ;
   } else {
    for ( oy1 = 0 ; oy1 + 512 < img_yl1 ; oy1 += 512 ) {
      x_read_bmp_image8 ( oy1 , 512 ) ;
      x_mark_diff_point4 ( oy1 , 512 ) ;
      x_compress4 ( oy1 , 512 ) ;
    }

    syl1 = img_yl1 - oy1 ;
    x_read_bmp_image8 ( oy1 , syl1 ) ;
    x_mark_diff_point4 ( oy1 , syl1 ) ;
    x_compress4 ( oy1 , syl1 ) ;
  }

  if ( verbose_mode != 0 ) printf ( "\n" ) ;
  free ( img_buf8 ) ;
  img_buf8 = NULL ;
  free ( edge_map1 ) ;
  edge_map1 = NULL ;
  return ( 0 ) ;

lb800 :
  if ( img_buf8  != NULL ) free ( img_buf8  ) ;
  if ( edge_map1 != NULL ) free ( edge_map1 ) ;
  return ( - 1 ) ;
}

/* ---------------------------------------------------------------- */

static int x_bmp_pic_conv8 ( void )
{
  int big_img_sw1 , oy1 , syl1 ;
  ulongg img_xl1 , img_yl1 ;
  ulongg buf_sz1 ;

  edge_map1 = NULL ;
  img_buf8 = NULL ;
  big_img_sw1 = 0 ;

  if ( setjmp ( wenv1 ) != 0 ) goto lb800 ;
  x_write_hdr ( 8 ) ;
  x_conv_palette ( 8 ) ;

  img_xl1 = bmp_inf_hdr . biWidth ;
  img_yl1 = bmp_inf_hdr . biHeight ;

  buf_xb1 = ( img_xl1 + 3 ) & ~ 3 ;	/* BMP line width */
  buf_yl1 = img_yl1 ;

  if ( img_xl1 * img_yl1 > 1024 * 512 && img_yl1 > 512 ) {
    buf_yl1 = 512 ;
    big_img_sw1 = 1 ;
  }

  buf_sz1 = buf_xb1 * buf_yl1 ;
  edge_xb1 = ( img_xl1 + 7 ) >> 3 ;
  edge_sz1 = edge_xb1 * buf_yl1 ;

  if ( ( edge_map1 = malloc ( edge_sz1 ) ) == NULL ) {
    puts ( "edge_map can't alloc" ) ;
    goto lb800 ;
  }

  if ( ( img_buf8 = malloc ( buf_sz1 ) ) == NULL ) {
    puts ( "img_buf can't alloc" ) ;
    goto lb800 ;
  }

  if ( big_img_sw1 == 0 ) {
    x_read_bmp_image8 ( 0 , img_yl1 ) ;
    x_mark_diff_point8 ( 0 , img_yl1 ) ;
    x_compress8 ( 0 , img_yl1 ) ;
   } else {
    for ( oy1 = 0 ; oy1 + 512 < img_yl1 ; oy1 += 512 ) {
      x_read_bmp_image8 ( oy1 , 512 ) ;
      x_mark_diff_point8 ( oy1 , 512 ) ;
      x_compress8 ( oy1 , 512 ) ;
    }

    syl1 = img_yl1 - oy1 ;
    x_read_bmp_image8 ( oy1 , syl1 ) ;
    x_mark_diff_point8 ( oy1 , syl1 ) ;
    x_compress8 ( oy1 , syl1 ) ;
  }

  if ( verbose_mode != 0 ) printf ( "\n" ) ;
  free ( img_buf8 ) ;
  img_buf8 = NULL ;
  free ( edge_map1 ) ;
  edge_map1 = NULL ;
  return ( 0 ) ;

lb800 :
  if ( img_buf8  != NULL ) free ( img_buf8  ) ;
  if ( edge_map1 != NULL ) free ( edge_map1 ) ;
  return ( - 1 ) ;
}

/* ---------------------------------------------------------------- */

static int x_bmp_pic_conv24 ( void )
{
  int big_img_sw1 , oy1 , syl1 ;
  ulongg img_xl1 , img_yl1 ;
  ulongg buf_sz1 ;

  edge_map1 = NULL ;
  img_buf16 = NULL ;
  big_img_sw1 = 0 ;

  if ( setjmp ( wenv1 ) != 0 ) goto lb800 ;

  x_write_hdr ( 15 ) ;

  img_xl1 = bmp_inf_hdr . biWidth ;
  img_yl1 = bmp_inf_hdr . biHeight ;

  buf_xb1 = img_xl1 * sizeof ( * img_buf16 ) ;
  buf_yl1 = img_yl1 ;

  if ( img_xl1 * img_yl1 > 1024 * 512 && img_yl1 > 512 ) {
    buf_yl1 = 512 ;
    big_img_sw1 = 1 ;
  }

  buf_sz1 = buf_xb1 * buf_yl1 ;
  edge_xb1 = ( img_xl1 + 7 ) >> 3 ;
  edge_sz1 = edge_xb1 * buf_yl1 ;

  if ( ( edge_map1 = malloc ( edge_sz1 ) ) == NULL ) {
    puts ( "edge_map can't alloc" ) ;
    goto lb800 ;
  }

  if ( ( img_buf16 = malloc ( buf_sz1 ) ) == NULL ) {
    puts ( "img_buf can't alloc" ) ;
    goto lb800 ;
  }

  mk_cnvtbl ( ) ;
  x_init_color_cash ( ) ;

  if ( big_img_sw1 == 0 ) {
    x_read_bmp_image24 ( 0 , img_yl1 ) ;
    x_mark_diff_point16 ( 0 , img_yl1 ) ;
    x_compress15 ( 0 , img_yl1 ) ;
   } else {
    for ( oy1 = 0 ; oy1 + 512 < img_yl1 ; oy1 += 512 ) {
      x_read_bmp_image24 ( oy1 , 512 ) ;
      x_mark_diff_point16 ( oy1 , 512 ) ;
      x_compress15 ( oy1 , 512 ) ;
    }

    syl1 = img_yl1 - oy1 ;
    x_read_bmp_image24 ( oy1 , syl1 ) ;
    x_mark_diff_point16 ( oy1 , syl1 ) ;
    x_compress15 ( oy1 , syl1 ) ;
  }

  if ( verbose_mode != 0 ) printf ( "\n" ) ;
  free ( img_buf16 ) ;
  img_buf16 = NULL ;
  free ( edge_map1 ) ;
  edge_map1 = NULL ;
  return ( 0 ) ;

lb800 :
  if ( img_buf16 != NULL ) free ( img_buf16 ) ;
  if ( edge_map1 != NULL ) free ( edge_map1 ) ;
  return ( - 1 ) ;
}

/* ---------------------------------------------------------------- */

static void x_write_hdr ( int cl_bit1 )
{
  str_write ( "PIC/MM/XSS/:" ) ;
  bit_write ( 8 , 0x1A ) ;
  bit_write ( 8 , 0 ) ;
  bit_write ( 16 , 0 ) ;
  bit_write ( 16 , cl_bit1 ) ;
  bit_write ( 16 , bmp_inf_hdr . biWidth ) ;
  bit_write ( 16 , bmp_inf_hdr . biHeight ) ;
}

/* ---------------------------------------------------------------- */

static void str_write ( void * str_pt1 )
{
  char wch1 ;
  char * str_pt2 ;

  str_pt2 = str_pt1 ;
  while ( ( wch1 = * str_pt2 ++ ) != 0 ) bit_write ( 8 , wch1 ) ;
}

/* ---------------------------------------------------------------- */

static void x_conv_palette ( int cl_bit1 )
{
  int rgb_size1 , cl_max1 , cl_cnt1 , cl_cnt2 ;
  RGB_QUAD * rgb_pt1 ;

  if ( bmp_inf_hdr . biSize != sizeof ( bmp_inf_hdr ) ) {
    if ( fseek ( bmp_f , sizeof ( bmp_fil_hdr ) + bmp_inf_hdr . biSize ,
                          SEEK_SET ) < 0 ) {

      printf ( "%s can't seek (color table)\n" , bmp_fname_pt1 ) ;
      longjmp ( wenv1 , 1 ) ;
    }
  }

  cl_max1 = 1 << bmp_inf_hdr . biBitCount ;
  if ( ( cl_cnt1 = bmp_inf_hdr . biClrUsed ) == 0 || cl_cnt1 > cl_max1 ) {
    cl_cnt1 = cl_max1 ;
  }

  rgb_size1 = sizeof ( RGB_QUAD ) * cl_cnt1 ;
  rgb_pt1 = (RGB_QUAD*) alloca ( rgb_size1 ) ;

  if ( fread ( rgb_pt1 , 1,rgb_size1, bmp_f)  != rgb_size1 ) {
    printf ( "%s can't read (color table)\n" , bmp_fname_pt1 ) ;
    longjmp ( wenv1 , 1 ) ;
  }

  cl_cnt2 = ( 1 << cl_bit1 ) - cl_cnt1 ;

  while ( cl_cnt1 -- ) {
    bit_write ( 16 , ( RGB ( rgb_pt1 -> rgbRed   >> 3 ,
                           rgb_pt1 -> rgbGreen >> 3 ,
                           rgb_pt1 -> rgbBlue  >> 3 ) - 1 )) ;
    rgb_pt1 ++ ;
  }

  while ( cl_cnt2 -- ) bit_write ( 16 , 0 ) ;
}

/* ---------------------------------------------------------------- */

static void x_read_bmp_image8 ( int oy1 , int syl1 )
{
  ulongg wlen1 ;

  if ( fseek ( bmp_f , bmp_fil_hdr . bfOffBits +
               buf_xb1 * ( bmp_inf_hdr . biHeight - oy1 - syl1 ) ,
               SEEK_SET ) < 0 ) {

    printf ( "%s can't seek (image data)\n" , bmp_fname_pt1 ) ;
    goto lb800 ;
  }

  wlen1 = buf_xb1 * syl1 ;
  if ( fread ( img_buf8 , 1, wlen1, bmp_f ) != wlen1 ) {
    printf ( "%s can't read (image data)\n" , bmp_fname_pt1 ) ;
    goto lb800 ;
  }
  return ;

lb800 :
  longjmp ( wenv1 , 1 ) ;
}

/* ---------------------------------------------------------------- */

static void x_mark_diff_point1 ( int oy1 , int syl1 )
{
  int sy1 , bx1 , xcnt1 ;
  ulongg img_xl1 ;
  char cl1 , cl2 , wch1 , wedge1 , wverbose1 ;
  char * edge_map_pt1 ;
  char * img_buf_pt1 ;

  cl1 = 0 ;
  sy1 = syl1 ;
  img_xl1 = bmp_inf_hdr . biWidth ;
  edge_map_pt1 = edge_map1 + syl1 * edge_xb1 ;
  img_buf_pt1 = img_buf8 + syl1 * buf_xb1 ;
  wverbose1 = verbose_mode ;

  while ( -- sy1 >= 0 ) {
    edge_map_pt1 -= edge_xb1 ;
    img_buf_pt1 -= buf_xb1 ;
    if ( wverbose1 != 0 ) printf ( "\rd line = %d " , ++ oy1 ) ;

    bx1 = 0 ;
    xcnt1 = img_xl1 >> 3 ;
    while ( xcnt1 -- ) {
      wch1 = img_buf_pt1 [ bx1 ] ;
      wedge1 = ( wch1 >> 1 ) ^ wch1 ;
      if ( cl1 != 0 ) wedge1 ^= 0x80 ;
      edge_map_pt1 [ bx1 ] = wedge1 ;
      cl1 = wch1 & 1 ;
      bx1 ++ ;
    }

    if ( ( xcnt1 = img_xl1 & 7 ) != 0 ) {
      wch1 = img_buf_pt1 [ bx1 ] ;
      wedge1 = ( wch1 >> 1 ) ^ wch1 ;
      if ( cl1 != 0 ) wedge1 ^= 0x80 ;
      edge_map_pt1 [ bx1 ] = wedge1 ;
      cl1 = ( wch1 >> ( 8 - xcnt1 ) ) & 1 ;
    }
  }
}

/* ---------------------------------------------------------------- */

static void x_compress1 ( int oy1 , int syl1 )
{
  int sx1 , sy1 , bx1 , xcnt1 ;
  ulongg img_xl1 ;
  char cl1 , wedge1 , wmask1 , wverbose1 ;
  int wlen1 ;
  char * edge_map_pt1 ;
  char * img_buf_pt1 ;

  wlen1 = 0 ;
  sy1 = syl1 ;
  img_xl1 = bmp_inf_hdr . biWidth ;
  edge_map_pt1 = edge_map1 + syl1 * edge_xb1 ;
  img_buf_pt1 = img_buf8 + syl1 * buf_xb1 ;
  wverbose1 = verbose_mode ;

  while ( -- sy1 >= 0 ) {
    edge_map_pt1 -= edge_xb1 ;
    img_buf_pt1 -= buf_xb1 ;
    if ( wverbose1 != 0 ) printf ( "\rc line = %d " , ++ oy1 ) ;

    sx1 = 0 ;
    bx1 = 0 ;
    xcnt1 = img_xl1 >> 3 ;
    while ( xcnt1 -- ) {
      wedge1 = edge_map_pt1 [ bx1 ] ;
      for ( wmask1 = 0x80 ; wmask1 != 0 ; wmask1 >>= 1 ) {
        wlen1 ++ ;
        if ( ( wedge1 & wmask1 ) != 0 ) {
          cl1 = ( img_buf_pt1 [ bx1 ] & wmask1 ) != 0 ;
          write_len ( wlen1 ) ;
          bit_write ( 4 , cl1 ) ;
          x_compress_chain1 ( sx1 , sy1 , edge_map_pt1 , img_buf_pt1 , cl1 ) ;
          wlen1 = 0 ;
        }
        sx1 ++ ;
      }
      bx1 ++ ;
    }

    if ( ( xcnt1 = img_xl1 & 7 ) != 0 ) {
      wedge1 = edge_map_pt1 [ bx1 ] ;
      wmask1 = 0x80 ;
      while ( xcnt1 -- ) {
        wlen1 ++ ;
        if ( ( wedge1 & wmask1 ) != 0 ) {
          cl1 = ( img_buf_pt1 [ bx1 ] & wmask1 ) != 0 ;
          write_len ( wlen1 ) ;
          bit_write ( 4 , cl1 ) ;
          x_compress_chain1 ( sx1 , sy1 , edge_map_pt1 , img_buf_pt1 , cl1 ) ;
          wlen1 = 0 ;
        }
        sx1 ++ ;
        wmask1 >>= 1 ;
      }
    }
  }

  write_len ( wlen1 + 1 ) ;
}

/* ---------------------------------------------------------------- */

static void x_compress_chain1 ( int sx1 , int sy1 ,
    char * edge_map_pt1 , char * img_buf_pt1 , char cl1 )
{
  int fsw1 , wlen1 , wdata1 ;
  ulongg img_xl1 ;
  char wmask1 ;

  fsw1 = 0 ;
  img_xl1 = bmp_inf_hdr . biWidth ;

  while ( sy1 -- ) {
    edge_map_pt1 -= edge_xb1 ;
    img_buf_pt1 -= buf_xb1 ;

    wmask1 = 0x80 >> ( sx1 & 7 ) ;
    if ( ( edge_map_pt1 [ sx1 >> 3 ] & wmask1 ) != 0 &&
        ( ( img_buf_pt1 [ sx1 >> 3 ] & wmask1 ) != 0 ) == cl1 ) {
      wlen1 = 2 ;
      wdata1 = 2 ;
    } else if ( -- sx1 >= 0         && ( wmask1 = 0x80 >> ( sx1 & 7 ) ,
         ( edge_map_pt1 [ sx1 >> 3 ] & wmask1 ) != 0 ) &&
        ( ( img_buf_pt1 [ sx1 >> 3 ] & wmask1 ) != 0 ) == cl1 ) {
      wlen1 = 2 ;
      wdata1 = 1 ;
    } else if ( ( sx1 += 2 ) < img_xl1 && ( wmask1 = 0x80 >> ( sx1 & 7 ) ,
         ( edge_map_pt1 [ sx1 >> 3 ] & wmask1 ) != 0 ) &&
        ( ( img_buf_pt1 [ sx1 >> 3 ] & wmask1 ) != 0 ) == cl1 ) {
      wlen1 = 2 ;
      wdata1 = 3 ;
    } else if ( ( sx1 -= 3 ) >= 0   && ( wmask1 = 0x80 >> ( sx1 & 7 ) ,
         ( edge_map_pt1 [ sx1 >> 3 ] & wmask1 ) != 0 ) &&
        ( ( img_buf_pt1 [ sx1 >> 3 ] & wmask1 ) != 0 ) == cl1 ) {
      wlen1 = 4 ;
      wdata1 = 2 ;
    } else if ( ( sx1 += 4 ) < img_xl1 && ( wmask1 = 0x80 >> ( sx1 & 7 ) ,
         ( edge_map_pt1 [ sx1 >> 3 ] & wmask1 ) != 0 ) &&
        ( ( img_buf_pt1 [ sx1 >> 3 ] & wmask1 ) != 0 ) == cl1 ) {
      wlen1 = 4 ;
      wdata1 = 3 ;
    } else {
      break ;
    }

    edge_map_pt1 [ sx1 >> 3 ] &= ~ wmask1 ;
    if ( fsw1 == 0 ) {
      bit_write ( 1 , 1 ) ;
      fsw1 = 1 ;
    }
    bit_write ( wlen1 , wdata1 ) ;
  }

  if ( fsw1 == 0 ) {
    bit_write ( 1 , 0 ) ;
   } else {
    bit_write ( 3 , 0 ) ;
  }
}

/* ---------------------------------------------------------------- */

static void x_mark_diff_point4 ( int oy1 , int syl1 )
{
  int sx1 , sy1 , xcnt1 , bx1 ;
  ulongg img_xl1 ;
  char cl1 , cl2 , wch1 , wverbose1 ;
  char * edge_map_pt1 ;
  char * img_buf_pt1 ;

  memset ( edge_map1 , 0 , edge_sz1 ) ;

  cl1 = 0 ;
  sy1 = syl1 ;
  img_xl1 = bmp_inf_hdr . biWidth ;
  edge_map_pt1 = edge_map1 + syl1 * edge_xb1 ;
  img_buf_pt1 = img_buf8 + syl1 * buf_xb1 ;
  wverbose1 = verbose_mode ;

  while ( -- sy1 >= 0 ) {
    edge_map_pt1 -= edge_xb1 ;
    img_buf_pt1 -= buf_xb1 ;
    if ( wverbose1 != 0 ) printf ( "\rd line = %d " , ++ oy1 ) ;

    sx1 = 0 ;
    xcnt1 = img_xl1 >> 1 ;
    bx1 = 0 ;

    while ( xcnt1 -- ) {
      wch1 = img_buf_pt1 [ bx1 ++ ] ;
      cl2 = wch1 >> 4 ;
      if ( cl2 != cl1 ) {
        cl1 = cl2 ;
        edge_map_pt1 [ sx1 >> 3 ] |= 1 << ( sx1 & 7 ) ;
      }
      sx1 ++ ;

      cl2 = wch1 & 0xF ;
      if ( cl2 != cl1 ) {
        cl1 = cl2 ;
        edge_map_pt1 [ sx1 >> 3 ] |= 1 << ( sx1 & 7 ) ;
      }
      sx1 ++ ;
    }

    if ( ( img_xl1 & 1 ) != 0 ) {
      cl2 = img_buf_pt1 [ bx1 ] >> 4 ;
      if ( cl2 != cl1 ) {
        edge_map_pt1 [ sx1 >> 3 ] |= 1 << ( sx1 & 7 ) ;
      }
    }
  }
}

/* ---------------------------------------------------------------- */

static void x_compress4 ( int oy1 , int syl1 )
{
  int sx1 , sy1 , bx1 , xcnt1 ;
  ulongg img_xl1 ;
  char cl1 , wedge1 , wmask1 , wverbose1 ;
  int wlen1 ;
  char * edge_map_pt1 ;
  char * img_buf_pt1 ;

  wlen1 = 0 ;
  sy1 = syl1 ;
  img_xl1 = bmp_inf_hdr . biWidth ;
  edge_map_pt1 = edge_map1 + syl1 * edge_xb1 ;
  img_buf_pt1 = img_buf8 + syl1 * buf_xb1 ;
  wverbose1 = verbose_mode ;

  while ( -- sy1 >= 0 ) {
    edge_map_pt1 -= edge_xb1 ;
    img_buf_pt1 -= buf_xb1 ;
    if ( wverbose1 != 0 ) printf ( "\rc line = %d " , ++ oy1 ) ;

    sx1 = 0 ;
    bx1 = 0 ;
    xcnt1 = img_xl1 >> 3 ;
    while ( xcnt1 -- ) {
      wedge1 = edge_map_pt1 [ bx1 ] ;
      for ( wmask1 = 1 ; wmask1 != 0 ; wmask1 <<= 1 ) {
        wlen1 ++ ;
        if ( ( wedge1 & wmask1 ) != 0 ) {
          cl1 = img_buf_pt1 [ sx1 >> 1 ] ;
          if ( ( sx1 & 1 ) == 0 ) {
            cl1 >>= 4 ;
           } else {
            cl1 &= 0xF ;
          }

          write_len ( wlen1 ) ;
          bit_write ( 4 , cl1 ) ;
          x_compress_chain4 ( sx1 , sy1 , edge_map_pt1 , img_buf_pt1 , cl1 ) ;
          wlen1 = 0 ;
        }
        sx1 ++ ;
      }
      bx1 ++ ;
    }

    if ( ( xcnt1 = img_xl1 & 7 ) != 0 ) {
      wedge1 = edge_map_pt1 [ bx1 ] ;
      wmask1 = 1 ;
      while ( xcnt1 -- ) {
        wlen1 ++ ;
        if ( ( wedge1 & wmask1 ) != 0 ) {
          cl1 = img_buf_pt1 [ sx1 >> 1 ] ;
          if ( ( sx1 & 1 ) == 0 ) {
            cl1 >>= 4 ;
           } else {
            cl1 &= 0xF ;
          }

          write_len ( wlen1 ) ;
          bit_write ( 4 , cl1 ) ;
          x_compress_chain4 ( sx1 , sy1 , edge_map_pt1 , img_buf_pt1 , cl1 ) ;
          wlen1 = 0 ;
        }
        sx1 ++ ;
        wmask1 <<= 1 ;
      }
    }
  }

  write_len ( wlen1 + 1 ) ;
}

/* ---------------------------------------------------------------- */

static void x_compress_chain4 ( int sx1 , int sy1 ,
    char * edge_map_pt1 , char * img_buf_pt1 , char cl1 )
{
  int fsw1 , wlen1 , wdata1 ;
  ulongg img_xl1 ;
  char cl_mask1 , cl2 ;

  if ( ( sx1 & 1 ) == 0 ) {
    cl_mask1 = 0xF0 ;
   } else {
    cl_mask1 = 0x0F ;
  }

  cl2 = ( cl1 << 4 ) | cl1 ;
  fsw1 = 0 ;
  img_xl1 = bmp_inf_hdr . biWidth ;

  while ( sy1 -- ) {
    edge_map_pt1 -= edge_xb1 ;
    img_buf_pt1 -= buf_xb1 ;

    if ( ( edge_map_pt1 [ sx1 >> 3 ] & ( 1 << ( sx1 & 7 ) ) ) != 0 &&
        ( ( img_buf_pt1 [ sx1 >> 1 ] ^ cl2 ) & cl_mask1 ) == 0 ) {
      wlen1 = 2 ;
      wdata1 = 2 ;
    } else if ( ( cl_mask1 = ~ cl_mask1 , -- sx1 ) >= 0 &&
         ( edge_map_pt1 [ sx1 >> 3 ] & ( 1 << ( sx1 & 7 ) ) ) != 0 &&
        ( ( img_buf_pt1 [ sx1 >> 1 ] ^ cl2 ) & cl_mask1 ) == 0 ) {
      wlen1 = 2 ;
      wdata1 = 1 ;
    } else if ( ( sx1 += 2 ) < img_xl1 &&
         ( edge_map_pt1 [ sx1 >> 3 ] & ( 1 << ( sx1 & 7 ) ) ) != 0 &&
        ( ( img_buf_pt1 [ sx1 >> 1 ] ^ cl2 ) & cl_mask1 ) == 0 ) {
      wlen1 = 2 ;
      wdata1 = 3 ;
    } else if ( ( cl_mask1 = ~ cl_mask1 , sx1 -= 3 ) >= 0 &&
         ( edge_map_pt1 [ sx1 >> 3 ] & ( 1 << ( sx1 & 7 ) ) ) != 0 &&
        ( ( img_buf_pt1 [ sx1 >> 1 ] ^ cl2 ) & cl_mask1 ) == 0 ) {
      wlen1 = 4 ;
      wdata1 = 2 ;
    } else if ( ( sx1 += 4 ) < img_xl1 &&
         ( edge_map_pt1 [ sx1 >> 3 ] & ( 1 << ( sx1 & 7 ) ) ) != 0 &&
        ( ( img_buf_pt1 [ sx1 >> 1 ] ^ cl2 ) & cl_mask1 ) == 0 ) {
      wlen1 = 4 ;
      wdata1 = 3 ;
    } else {
      break ;
    }

    edge_map_pt1 [ sx1 >> 3 ] &= ~ ( 1 << ( sx1 & 7 ) ) ;
    if ( fsw1 == 0 ) {
      bit_write ( 1 , 1 ) ;
      fsw1 = 1 ;
    }
    bit_write ( wlen1 , wdata1 ) ;
  }

  if ( fsw1 == 0 ) {
    bit_write ( 1 , 0 ) ;
   } else {
    bit_write ( 3 , 0 ) ;
  }
}

/* ---------------------------------------------------------------- */

static void x_mark_diff_point8 ( int oy1 , int syl1 )
{
  int sx1 , sy1 ;
  ulongg img_xl1 ;
  char cl1 , cl2 , wverbose1 ;
  char * edge_map_pt1 ;
  char * img_buf_pt1 ;

  memset ( edge_map1 , 0 , edge_sz1 ) ;

  cl1 = 0 ;
  sy1 = syl1 ;
  img_xl1 = bmp_inf_hdr . biWidth ;
  edge_map_pt1 = edge_map1 + syl1 * edge_xb1 ;
  img_buf_pt1 = img_buf8 + syl1 * buf_xb1 ;
  wverbose1 = verbose_mode ;

  while ( -- sy1 >= 0 ) {
    edge_map_pt1 -= edge_xb1 ;
    img_buf_pt1 -= buf_xb1 ;
    if ( wverbose1 != 0 ) printf ( "\rd line = %d " , ++ oy1 ) ;

    for ( sx1 = 0 ; sx1 < img_xl1 ; sx1 ++ ) {
      if ( ( cl2 = img_buf_pt1 [ sx1 ] ) != cl1 ) {
        cl1 = cl2 ;
        edge_map_pt1 [ sx1 >> 3 ] |= 1 << ( sx1 & 7 ) ;
      }
    }
  }
}

/* ---------------------------------------------------------------- */

static void x_compress8 ( int oy1 , int syl1 )
{
  int sx1 , sy1 , bx1 , xcnt1 ;
  ulongg img_xl1 ;
  char cl1 , wedge1 , wmask1 , wverbose1 ;
  int wlen1 ;
  char * edge_map_pt1 ;
  char * img_buf_pt1 ;

  wlen1 = 0 ;
  sy1 = syl1 ;
  img_xl1 = bmp_inf_hdr . biWidth ;
  edge_map_pt1 = edge_map1 + syl1 * edge_xb1 ;
  img_buf_pt1 = img_buf8 + syl1 * buf_xb1 ;
  wverbose1 = verbose_mode ;

  while ( -- sy1 >= 0 ) {
    edge_map_pt1 -= edge_xb1 ;
    img_buf_pt1 -= buf_xb1 ;
    if ( wverbose1 != 0 ) printf ( "\rc line = %d " , ++ oy1 ) ;

    sx1 = 0 ;
    bx1 = 0 ;
    xcnt1 = img_xl1 >> 3 ;
    while ( xcnt1 -- ) {
      wedge1 = edge_map_pt1 [ bx1 ] ;
      for ( wmask1 = 1 ; wmask1 != 0 ; wmask1 <<= 1 ) {
        wlen1 ++ ;
        if ( ( wedge1 & wmask1 ) != 0 ) {
          cl1 = img_buf_pt1 [ sx1 ] ;
          write_len ( wlen1 ) ;
          bit_write ( 8 , cl1 ) ;
          x_compress_chain8 ( sx1 , sy1 , edge_map_pt1 , img_buf_pt1 , cl1 ) ;
          wlen1 = 0 ;
        }
        sx1 ++ ;
      }
      bx1 ++ ;
    }

    if ( ( xcnt1 = img_xl1 & 7 ) != 0 ) {
      wedge1 = edge_map_pt1 [ bx1 ] ;
      wmask1 = 1 ;
      while ( xcnt1 -- ) {
        wlen1 ++ ;
        if ( ( wedge1 & wmask1 ) != 0 ) {
          cl1 = img_buf_pt1 [ sx1 ] ;
          write_len ( wlen1 ) ;
          bit_write ( 8 , cl1 ) ;
          x_compress_chain8 ( sx1 , sy1 , edge_map_pt1 , img_buf_pt1 , cl1 ) ;
          wlen1 = 0 ;
        }
        sx1 ++ ;
        wmask1 <<= 1 ;
      }
    }
  }

  write_len ( wlen1 + 1 ) ;
}

/* ---------------------------------------------------------------- */

static void x_compress_chain8 ( int sx1 , int sy1 ,
    char * edge_map_pt1 , char * img_buf_pt1 , char cl1 )
{
  int fsw1 , wlen1 , wdata1 ;
  ulongg img_xl1 ;

  fsw1 = 0 ;
  img_xl1 = bmp_inf_hdr . biWidth ;

  while ( sy1 -- ) {
    edge_map_pt1 -= edge_xb1 ;
    img_buf_pt1 -= buf_xb1 ;

    if ( ( edge_map_pt1 [ sx1 >> 3 ] & ( 1 << ( sx1 & 7 ) ) ) != 0 &&
            img_buf_pt1 [ sx1 ] == cl1 ) {
      wlen1 = 2 ;
      wdata1 = 2 ;
    } else if ( -- sx1 >= 0 &&
         ( edge_map_pt1 [ sx1 >> 3 ] & ( 1 << ( sx1 & 7 ) ) ) != 0 &&
            img_buf_pt1 [ sx1 ] == cl1 ) {
      wlen1 = 2 ;
      wdata1 = 1 ;
    } else if ( ( sx1 += 2 ) < img_xl1 &&
         ( edge_map_pt1 [ sx1 >> 3 ] & ( 1 << ( sx1 & 7 ) ) ) != 0 &&
            img_buf_pt1 [ sx1 ] == cl1 ) {
      wlen1 = 2 ;
      wdata1 = 3 ;
    } else if ( ( sx1 -= 3 ) >= 0 &&
         ( edge_map_pt1 [ sx1 >> 3 ] & ( 1 << ( sx1 & 7 ) ) ) != 0 &&
            img_buf_pt1 [ sx1 ] == cl1 ) {
      wlen1 = 4 ;
      wdata1 = 2 ;
    } else if ( ( sx1 += 4 ) < img_xl1 &&
         ( edge_map_pt1 [ sx1 >> 3 ] & ( 1 << ( sx1 & 7 ) ) ) != 0 &&
            img_buf_pt1 [ sx1 ] == cl1 ) {
      wlen1 = 4 ;
      wdata1 = 3 ;
    } else {
      break ;
    }

    edge_map_pt1 [ sx1 >> 3 ] &= ~ ( 1 << ( sx1 & 7 ) ) ;
    if ( fsw1 == 0 ) {
      bit_write ( 1 , 1 ) ;
      fsw1 = 1 ;
    }
    bit_write ( wlen1 , wdata1 ) ;
  }

  if ( fsw1 == 0 ) {
    bit_write ( 1 , 0 ) ;
   } else {
    bit_write ( 3 , 0 ) ;
  }
}

/* ---------------------------------------------------------------- */

static void x_read_bmp_image24 ( int oy1 , int syl1 )
{
  ulongg img_xl1 , bmp_xb1 ;
  char * bmp_buf1 ;
  PIXEL * img_pt1 ;

  img_xl1 = bmp_inf_hdr . biWidth ;
  bmp_xb1 = ( img_xl1 * 3 + 3 ) & ~ 3 ;		/* BMP line width */
  bmp_buf1 = (char*) alloca ( bmp_xb1 ) ;

  if ( fseek ( bmp_f , bmp_fil_hdr . bfOffBits +
               bmp_xb1 * ( bmp_inf_hdr . biHeight - oy1 - syl1 ) ,
               SEEK_SET ) < 0 ) goto lb600 ;

  img_pt1 = img_buf16 ;
  while ( syl1 -- ) {
    if ( fread ( bmp_buf1 , 1, bmp_xb1, bmp_f ) != bmp_xb1 ) goto lb610 ;
    x_conv_line24 ( img_pt1 , bmp_buf1 , img_xl1 ) ;
    img_pt1 += img_xl1 ;
  }
  return ;

lb600 :
  printf ( "%s can't seek (image data)\n" , bmp_fname_pt1 ) ;
  goto lb800 ;

lb610 :
  printf ( "%s can't read (image data)\n" , bmp_fname_pt1 ) ;
  goto lb800 ;

lb800 :
  longjmp ( wenv1 , 1 ) ;
}

/* ---------------------------------------------------------------- */

static void mk_cnvtbl ( void )
{
  int ix1 ;

  for ( ix1 = 0 ; ix1 < 256 ; ix1 ++ ) {
    red_cnv_tbl   [ ix1 ] = RGB ( ix1 >> ( 8 - 5 ) , 0 , 0 ) - 1 ;
    green_cnv_tbl [ ix1 ] = RGB ( 0 , ix1 >> ( 8 - 5 ) , 0 ) - 1 ;
    blue_cnv_tbl  [ ix1 ] = RGB ( 0 , 0 , ix1 >> ( 8 - 5 ) ) - 1 ;
  }
}

/* ---------------------------------------------------------------- */

static void x_conv_line24 ( PIXEL * img_pt1 , char * bmp_pt1 , int sxl1 )
{
  int wred1 , wgreen1 , wblue1 ;

  while ( sxl1 -- ) {
    wblue1  = * bmp_pt1 ++ ;
    wgreen1 = * bmp_pt1 ++ ;
    wred1   = * bmp_pt1 ++ ;

    * img_pt1 ++ = 
        red_cnv_tbl   [ wred1   ] +
        green_cnv_tbl [ wgreen1 ] +
        blue_cnv_tbl  [ wblue1  ] ;
  }
}

/* ----------------------------------------------------------------- */

static void x_init_color_cash ( void )
{
  int ix1 ;

  for ( ix1 = 0 ; ix1 < 128 ; ix1 ++ ) {
    cl_cache [ ix1 ] . color = 0 ;
    cl_cache [ ix1 ] . prev = ix1 + 1 ;
    cl_cache [ ix1 ] . next = ix1 - 1 ;
  }

  cl_cache [ 127 ] . prev = 0 ;
  cl_cache [ 0 ] . next = 127 ;
  cur_cl_ix = 0 ;
}

/* ---------------------------------------------------------------- */

static void x_mark_diff_point16 ( int oy1 , int syl1 )
{
  int sx1 , sy1 ;
  ulongg img_xl1 ;
  PIXEL cl1 , cl2 ;
  char wverbose1 ;
  char * edge_map_pt1 ;
  PIXEL * img_buf_pt1 ;

  memset ( edge_map1 , 0 , edge_sz1 ) ;

  cl1 = 0 ;
  sy1 = syl1 ;
  img_xl1 = bmp_inf_hdr . biWidth ;
  edge_map_pt1 = edge_map1 + syl1 * edge_xb1 ;
  img_buf_pt1 = img_buf16 + syl1 * img_xl1 ;
  wverbose1 = verbose_mode ;

  while ( -- sy1 >= 0 ) {
    edge_map_pt1 -= edge_xb1 ;
    img_buf_pt1 -= img_xl1 ;
    if ( wverbose1 != 0 ) printf ( "\rd line = %d " , ++ oy1 ) ;

    for ( sx1 = 0 ; sx1 < img_xl1 ; sx1 ++ ) {
      if ( ( cl2 = img_buf_pt1 [ sx1 ] ) != cl1 ) {
        cl1 = cl2 ;
        edge_map_pt1 [ sx1 >> 3 ] |= 1 << ( sx1 & 7 ) ;
      }
    }
  }
}

/* ---------------------------------------------------------------- */

static void x_compress15 ( int oy1 , int syl1 )
{
  int sx1 , sy1 , bx1 , xcnt1 ;
  ulongg img_xl1 ;
  PIXEL cl1 ;
  char wedge1 , wmask1 , wverbose1 ;
  int wlen1 ;
  char * edge_map_pt1 ;
  PIXEL * img_buf_pt1 ;

  wlen1 = 0 ;
  sy1 = syl1 ;
  img_xl1 = bmp_inf_hdr . biWidth ;
  edge_map_pt1 = edge_map1 + syl1 * edge_xb1 ;
  img_buf_pt1 = img_buf16 + syl1 * img_xl1 ;
  wverbose1 = verbose_mode ;

  while ( -- sy1 >= 0 ) {
    edge_map_pt1 -= edge_xb1 ;
    img_buf_pt1 -= img_xl1 ;
    if ( wverbose1 != 0 ) printf ( "\rc line = %d " , ++ oy1 ) ;

    sx1 = 0 ;
    bx1 = 0 ;
    xcnt1 = img_xl1 >> 3 ;
    while ( xcnt1 -- ) {
      wedge1 = edge_map_pt1 [ bx1 ] ;
      for ( wmask1 = 1 ; wmask1 != 0 ; wmask1 <<= 1 ) {
        wlen1 ++ ;
        if ( ( wedge1 & wmask1 ) != 0 ) {
          cl1 = img_buf_pt1 [ sx1 ] ;
          write_len ( wlen1 ) ;
          write_color15 ( cl1 ) ;
          x_compress_chain15 ( sx1 , sy1 , edge_map_pt1 , img_buf_pt1 , cl1 ) ;
          wlen1 = 0 ;
        }
        sx1 ++ ;
      }
      bx1 ++ ;
    }

    if ( ( xcnt1 = img_xl1 & 7 ) != 0 ) {
      wedge1 = edge_map_pt1 [ bx1 ] ;
      wmask1 = 1 ;
      while ( xcnt1 -- ) {
        wlen1 ++ ;
        if ( ( wedge1 & wmask1 ) != 0 ) {
          cl1 = img_buf_pt1 [ sx1 ] ;
          write_len ( wlen1 ) ;
          write_color15 ( cl1 ) ;
          x_compress_chain15 ( sx1 , sy1 , edge_map_pt1 , img_buf_pt1 , cl1 ) ;
          wlen1 = 0 ;
        }
        sx1 ++ ;
        wmask1 <<= 1 ;
      }
    }
  }

  write_len ( wlen1 + 1 ) ;
}

/* ---------------------------------------------------------------- */

static void x_compress_chain15 ( int sx1 , int sy1 ,
    char * edge_map_pt1 , PIXEL * img_buf_pt1 , PIXEL cl1 )
{
  int fsw1 , wlen1 , wdata1 ;
  ulongg img_xl1 ;

  fsw1 = 0 ;
  img_xl1 = bmp_inf_hdr . biWidth ;

  while ( sy1 -- ) {
    edge_map_pt1 -= edge_xb1 ;
    img_buf_pt1 -= img_xl1 ;

    if ( ( edge_map_pt1 [ sx1 >> 3 ] & ( 1 << ( sx1 & 7 ) ) ) != 0 &&
            img_buf_pt1 [ sx1 ] == cl1 ) {
      wlen1 = 2 ;
      wdata1 = 2 ;
    } else if ( -- sx1 >= 0 &&
         ( edge_map_pt1 [ sx1 >> 3 ] & ( 1 << ( sx1 & 7 ) ) ) != 0 &&
            img_buf_pt1 [ sx1 ] == cl1 ) {
      wlen1 = 2 ;
      wdata1 = 1 ;
    } else if ( ( sx1 += 2 ) < img_xl1 &&
         ( edge_map_pt1 [ sx1 >> 3 ] & ( 1 << ( sx1 & 7 ) ) ) != 0 &&
            img_buf_pt1 [ sx1 ] == cl1 ) {
      wlen1 = 2 ;
      wdata1 = 3 ;
    } else if ( ( sx1 -= 3 ) >= 0 &&
         ( edge_map_pt1 [ sx1 >> 3 ] & ( 1 << ( sx1 & 7 ) ) ) != 0 &&
            img_buf_pt1 [ sx1 ] == cl1 ) {
      wlen1 = 4 ;
      wdata1 = 2 ;
    } else if ( ( sx1 += 4 ) < img_xl1 &&
         ( edge_map_pt1 [ sx1 >> 3 ] & ( 1 << ( sx1 & 7 ) ) ) != 0 &&
            img_buf_pt1 [ sx1 ] == cl1 ) {
      wlen1 = 4 ;
      wdata1 = 3 ;
    } else {
      break ;
    }

    edge_map_pt1 [ sx1 >> 3 ] &= ~ ( 1 << ( sx1 & 7 ) ) ;
    if ( fsw1 == 0 ) {
      bit_write ( 1 , 1 ) ;
      fsw1 = 1 ;
    }
    bit_write ( wlen1 , wdata1 ) ;
  }

  if ( fsw1 == 0 ) {
    bit_write ( 1 , 0 ) ;
   } else {
    bit_write ( 3 , 0 ) ;
  }
}

/* ---------------------------------------------------------------- */

static void write_len ( int n )
{
  int wlen1 ;
  int lwk1 ;

  wlen1 = 1 ;
  lwk1 = 4 ;
  n ++ ;

  while ( n >= lwk1 ) {
    wlen1 ++ ;
    lwk1 <<= 1 ;
  }

  // bit_write ( wlen1 , swap_int(( ( 1 << wlen1 ) - 1 ) & ~ 1 )) ;
  // bit_write ( wlen1 , swap_int( n - ( lwk1 >> 1 ) )) ;

  bit_write ( wlen1 , ( ( 1 << wlen1 ) - 1 ) & ~ 1 ) ;
  bit_write ( wlen1 , n - ( lwk1 >> 1 ) ) ;
}

/* ----------------------------------------------------------------- */

static void write_color15 ( PIXEL cl1 )
{
  int ix1 ;

  if ( ( ix1 = search_col ( cl1 ) ) < 0 ) {
    bit_write ( 16 , cl1 >> 1 ) ;
   } else {
    bit_write ( 8 , ix1 + 0x80 ) ;
  }
}

/* ----------------------------------------------------------------- */

static int search_col ( PIXEL cl1 )
{
  int ix1 ;

  for ( ix1 = 0 ; ix1 < 128 ; ix1 ++ ) {
    if ( cl_cache [ ix1 ] . color == cl1 ) {
      set_color ( ix1 ) ;
      return ( ix1 ) ;
    }
  }

  cur_cl_ix = cl_cache [ cur_cl_ix ] . prev ;
  cl_cache [ cur_cl_ix ] . color = cl1 ;

  return ( - 1 ) ;
}

/* ----------------------------------------------------------------- */

static void set_color ( int ix1 )
{
  struct CL_CACHE * cl_cache_pt1 , * cl_cache_pt2 ;

  if ( cur_cl_ix != ix1 ) {
    cl_cache_pt1 = & cl_cache [ ix1 ] ;
    cl_cache_pt2 = & cl_cache [ cur_cl_ix ] ;

    cl_cache [ cl_cache_pt1 -> prev ] . next = cl_cache_pt1 -> next ;
    cl_cache [ cl_cache_pt1 -> next ] . prev = cl_cache_pt1 -> prev ;

    cl_cache_pt1 -> prev = cl_cache_pt2 -> prev ;
    cl_cache_pt1 -> next = cur_cl_ix ;

    cl_cache [ cl_cache_pt2 -> prev ] . next = ix1 ;
    cl_cache_pt2 -> prev = ix1 ;
    cur_cl_ix = ix1 ;
  }
}

/* ---------------------------------------------------------------- */
//THIS FUNCTION HAS BEEN FIXED
static void bit_write ( int wlen1 , ulongg wdata1 )
{
/*  wdata1 &= ( 1 << wlen1 ) - 1 ;  */

  if ( wlen1 >= bit_len ) {

    * pic_put_pt ++ = swap_ulongg(( pic_bit_data << bit_len ) | ( wdata1 >> ( wlen1 - bit_len ) )) ;
    // unsigned int off =wlen1-bit_len;
    // * pic_put_pt ++ = ( pic_bit_data ) | ( wdata1 << ( 32-bit_len ) );
    // pic_bit_data=0;

    if ( -- buff_len <= 0 ) {
      if ( fwrite ( pic_buf , 1,  sizeof ( pic_buf ), pic_f ) != sizeof ( pic_buf ) ) {
        printf ( "%s can't write\n" , pic_fname_pt1 ) ;
        longjmp ( wenv1 , 1 ) ;
      }
      pic_put_pt = pic_buf ;
      buff_len = numberof ( pic_buf ) ;
    }

    if ( ( wlen1 -= bit_len ) <= 0 ) {
      bit_len = 32 ;
      return ;
    }

    wdata1 &= ( 1 << wlen1 ) - 1 ;
    // wdata1 = wdata1>>off ;
    bit_len = 32 ;
  }

  pic_bit_data = ( pic_bit_data << wlen1 ) | wdata1 ;
  // pic_bit_data = ( pic_bit_data ) | (wdata1 <<(32-bit_len));
  bit_len -= wlen1 ;
}

/* ---------------------------------------------------------------- */

static void x_flush_buff ( void )
{
  int wlen1 ;

  if ( bit_len < 32 ) {
    * pic_put_pt = swap_ulongg( pic_bit_data << bit_len) ;
  }

  wlen1 = ( numberof ( pic_buf ) - buff_len ) * sizeof ( * pic_buf ) +
          ( ( ( 32 + 7 ) - bit_len ) >> 3 ) ;

  if ( wlen1 > 0 ) {
    if ( fwrite ( pic_buf , 1, wlen1 , pic_f ) != wlen1 ) {
      printf ( "%s can't write\n" , pic_fname_pt1 ) ;
      longjmp ( wenv1 , 1 ) ;
    }
  }
}

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
ulongg swap_ulongg( ulongg val )
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

/* ---------------------------------------------------------------- */

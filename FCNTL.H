/*
 * fcntl.h X68k XC Compiler v2.10 Copyright 1990,91,92 SHARP/Hudson
 */
#ifndef	__FCNTL_H
#define	__FCNTL_H

/************************************************************************/
/*	ストリーム入出力，低水準Ｉ／Ｏ関数用マクロ ２			*/
/************************************************************************/
#define	O_RDONLY	0x00000001	/*読み込み専用			*/
#define	O_WRONLY	0x00000002	/*書き込み専用			*/
#define	O_APPEND	0x00000004	/*アペンド・モード		*/
#define	O_RDWR		0x00000100	/*読み書き可能			*/
#define	O_BINARY	0x00000400	/*バイナリ・モード		*/
#define	O_TEXT		0x00000800	/*テキスト・モード		*/
#define	O_TRUNC		0x00001000	/*ファイル・サイズを０に切り詰め*/
#define	O_EXCL		0x00002000	/*ファイルが存在している時エラー*/
#define	O_CREAT		0x00004000	/*ファイルが存在しない時は作成	*/
#define	O_EOF		0x00008000	/*ＥＯＦに達したことを表す	*/

#define	STDIN	0
#define	STDOUT	1
#define	STDERR	2
#define	STDAUX	3
#define	STDPRN	4

#endif
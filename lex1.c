/* lex1.c         14 Feb 01; 31 May 12       */

/* This file contains code stubs for the lexical analyzer.
   Rename this file to be lexanc.c and fill in the stubs.    */

/* Copyright (c) 2001 Gordon S. Novak Jr. and
   The University of Texas at Austin. */

/*
    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include "token.h"
#include "lexan.h"

char *resprnt[] = { " ", "array", "begin", "case", "const", "do",
                           "downto", "else", "end", "file", "for",
		           "function", "goto", "if", "label", "nil",
                           "of", "packed", "procedure", "program", "record",
                           "repeat", "set", "then", "to", "type",
		           "until", "var", "while", "with" };

/* This file will work as given with an input file consisting only
   of integers separated by blanks:
   make lex1
   lex1
   12345 123    345  357
   */

/* Skip blanks and whitespace.  Expand this function to skip comments too. */
void skipblanks ()
  {
      int c;
      while ((c = peekchar()) != EOF && (c == ' ' || c == '\n' || c == '\t' || c == '{' || c == '(')){
		// { } comments
		if((c = peekchar()) == '{'){
			while((c = peekchar()) != '}'){
				getchar();
			}
		}
		// (* *) comments
		int loop = 1;
		if((c = peekchar()) == '(' && (c = peek2char()) == '*'){
			getchar();		// (
			while(loop){
				getchar(); 	// *
				if(peekchar() == '*' && peek2char() == ')'){		//exit
					getchar();	//grab *, then stop looping
					loop = 0;
				}
			}
		}
		getchar();	// will grab last ) and }
	  }
        
    }

/* Get identifiers and reserved words */
TOKEN identifier (TOKEN tok){
	char string[16];
	char c = getchar();			//grab first character of identifier
	int index = 0;
	while(CHARCLASS[c] == ALPHA || CHARCLASS[c] == NUMERIC){
		if(index < 15){
			string[index] = c;
			index++;
		}
		c = getchar();
	}
	string[index] = 0;
	string[15] = 0;				//oversized identifier special condition
	strcpy(tok->stringval, string);
	tok->tokentype = IDENTIFIERTOK;
	tok->datatype = STRINGTYPE;
	
	//now determine if reserved
	///
	int i = 1;
	for(; i < sizeof(resprnt)/sizeof(char*); i++){
		if(strcmp(resprnt[i], string) == 0){
			tok->tokentype = RESERVED;
			tok->datatype = STRINGTYPE;		//is this right for reserved??? CHECK!!!
			tok->whichval = i;
		}
	}
}

TOKEN getstring (TOKEN tok){			//assuming no empty strings, no s := ''
	char string[16];
	int index = 0, loop = 1;
	int c;
	getchar();							//grab first apostrophe
	while(loop){
		c = getchar();					//first character of string, assuming at least length 1
		//escaped apostrophe
		if(peekchar() == '\''){
			if(peek2char() != '\''){
				getchar();
				//if not at max string
				if(index < 15){
					string[index] = c;
					string[index+1] = 0;		//not escaped, null terminate string
				}
				loop = 0;
			}
			else{						//escaped, grab one apostrophe
				getchar();
				string[index] = c;
				index++;
			}
		}
		else{							//normal character
			//if not at max string
			if(index < 15){
				string[index] = c;
				index++;
			}
		}
		string[15] = 0;					//null terminate, special condition where string is too large
	}
	strcpy(tok->stringval, string);
	tok->tokentype = STRINGTOK;
	tok->datatype = STRINGTYPE;
	
}

TOKEN special (TOKEN tok)
  {
    }

/* Get and convert unsigned numbers of all types. */
TOKEN number (TOKEN tok)
  { long num;
    int  c, charval;
    num = 0;
    while ( (c = peekchar()) != EOF && CHARCLASS[c] == NUMERIC){   
		c = getchar();
		charval = (c - '0');
        num = num * 10 + charval;
    }
    tok->tokentype = NUMBERTOK;
    tok->datatype = INTEGER;
    tok->intval = num;
    return (tok);
  }


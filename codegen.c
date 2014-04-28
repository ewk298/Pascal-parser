/* codgen.c       Generate Assembly Code for x86         15 May 13   */

/* Copyright (c) 2013 Gordon S. Novak Jr. and The University of Texas at Austin
    */

/* Starter file for CS 375 Code Generation assignment.           */
/* Written by Gordon S. Novak Jr.                  */

/* This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License (file gpl.text) for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA. */

#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include "token.h"
#include "symtab.h"
#include "genasm.h"
#include "codegen.h"

#define NUM_I_REGS 4
#define NUM_F_REGS 16

void genc(TOKEN code);
void unmark_iregs();
void unmark_fregs();
void print_iregs();

int c_to_jmp[12] = {0, 0, 0, 0, 0, 0, JE, JNE, JL, JLE, JGE, JG};
//0 indicates register unused. EAX, ECX, EDX, EBX
int int_regs[4] = {0, 0, 0, 0};
//0 indicates register unused. xmm0 - xmm15
int f_regs[16] = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};

/* Set DEBUGGEN to 1 for debug printouts of code generation */
#define DEBUGGEN 0

int nextlabel;    /* Next available label number */
int stkframesize;   /* total stack frame size */

/* Top-level entry for code generator.
   pcode    = pointer to code:  (program foo (output) (progn ...))
   varsize  = size of local storage in bytes
   maxlabel = maximum label number used so far

Add this line to the end of your main program:
    gencode(parseresult, blockoffs[blocknumber], labelnumber);
The generated code is printed out; use a text editor to extract it for
your .s file.
         */

void gencode(TOKEN pcode, int varsize, int maxlabel)
  {  TOKEN name, code;
     name = pcode->operands;
     code = name->link->link;
     nextlabel = maxlabel + 1;
     stkframesize = asmentry(name->stringval,varsize);
     genc(code);
     asmexit(name->stringval);
  }

/* Trivial version: always returns RBASE + 0 */
/* Get a register.   */
/* Need a type parameter or two versions for INTEGER or REAL */
int getreg(int kind)
  {
	int index = 0;
	//IS WORD USED FOR INTEGER, DOUBLE CHECK
	if(kind == WORD){
		while(int_regs[index] == 1)
			index++;
		int_regs[index] = 1;
		return index;
	}
	
	else if(kind == FLOAT){
		while(f_regs[index] == 1)
			index++;
		f_regs[index] = 1;
		return index + FBASE;
	}
    /*     ***** fix this *****   */
     return RBASE;
  }

/* Trivial version */
/* Generate code for arithmetic expression, return a register number */
int genarith(TOKEN code)
  {   
	//printf("code tokentype: %d\n", code->tokentype);
	int num, reg, reg2, offs, labelnum;	
	SYMBOL sym;
	double realnum;
	TOKEN lhs, rhs;
     if (DEBUGGEN)
       { printf("genarith\n");
	 dbugprinttok(code);
       };
	switch ( code->tokentype ){ 
		case NUMBERTOK:
			switch (code->datatype){ 
				case INTEGER:
					num = code->intval;
					reg = getreg(WORD);
					if ( num >= MINIMMEDIATE && num <= MAXIMMEDIATE )
						asmimmed(MOVL, num, reg);
					break;
				case REAL:
				/*     ***** fix this *****   */
					realnum = code->realval;
					labelnum = nextlabel++;
					makeflit(realnum, labelnum);
					reg = getreg(FLOAT);
					if(num >= MINIMMEDIATE && num <= MAXIMMEDIATE)
						asmldflit(MOVSD, labelnum, reg);
					break;
			}
			break;
		case IDENTIFIERTOK:
			/*     ***** fix this *****   */	
			break;
		case OPERATOR:
			/*     ***** fix this *****   */
			//genc(code);
			//printf("code whichval: %d\n", code->whichval);
			switch(code->whichval){
				case FLOATOP:
					//printf("processing float\n");
					lhs = code->operands;
					reg = getreg(WORD);
					sym = lhs->symentry;
					offs = sym->offset - stkframesize;
					asmld(MOVL, offs, reg, lhs->stringval);
					reg2 = getreg(FLOAT);
					asmfloat(reg, reg2);
					reg = reg2;
					break;
					
				case TIMESOP:
					genc(code);
					break;
			}
			break;
	};
	return reg;
}


/* Generate code for a Statement from an intermediate-code form */
void genc(TOKEN code)
  {  TOKEN tok, lhs, rhs;
     int reg, reg2, offs;
     SYMBOL sym;
     if (DEBUGGEN)
       { printf("genc\n");
	 dbugprinttok(code);
       };
     if ( code->tokentype != OPERATOR )
        { printf("Bad code token");
	  dbugprinttok(code);
	};
	
	/* unmark_iregs();
	unmark_fregs(); */
     switch ( code->whichval )
       { case PROGNOP:
	   tok = code->operands;
	   while ( tok != NULL )
	     {  genc(tok);
		tok = tok->link;
	      };
	   break;
	 case ASSIGNOP:                   /* Trivial version: handles I := e */
		unmark_iregs();
		unmark_fregs();
	   lhs = code->operands;
	   rhs = lhs->link;
	   reg = genarith(rhs);              /* generate rhs into a register */
	   sym = lhs->symentry;              /* assumes lhs is a simple var  */
	   offs = sym->offset - stkframesize; /* net offset of the var   */
           switch (code->datatype)            /* store value into lhs  */
             { case INTEGER:
                 asmst(MOVL, reg, offs, lhs->stringval);
                 break;
                 /* ...  */
             };
           break;
	case LABELOP:
		asmlabel(code->operands->intval);
		break;
	
	case IFOP:
		unmark_iregs();
		unmark_fregs();
		//moves args to registers and generates cmp instruction. JMP uses condition code set by compare
		genc(code->operands);
		int op = code->operands->whichval;
		int thenlabel = nextlabel++;
		int elselabel = nextlabel++;
		asmjump(c_to_jmp[op], thenlabel);
		asmjump(JMP, elselabel);
		//then label
		asmlabel(thenlabel);
		genc(code->operands->link);
		//else label
		asmlabel(elselabel);
		break;
		
	case LEOP:
		unmark_iregs();
		unmark_fregs();
		lhs = code->operands;
		rhs = lhs->link;
		sym = lhs->symentry;
		offs = sym->offset - stkframesize;
		switch(code->datatype){
			case INTEGER:
				reg = getreg(WORD);
				asmld(MOVL, offs, reg, lhs->stringval);
				break;
		};
		reg2 = genarith(rhs);		//have rhs after lhs
		//generating compare
		asmrr(CMPL, reg2, reg);
		break;
		
	case TIMESOP:
		unmark_iregs();
		unmark_fregs();
		//printf("process timesop\n");
		lhs = code->operands;
		//printf("%d\n", lhs == NULL);
		rhs = lhs->link;
		//printf("%d\n", rhs == NULL);
		reg = genarith(lhs);
		reg2 = genarith(rhs);
		asmrr(MULSD, reg2, reg);
		break;
	
	case FLOATOP:
		//printf("processing floatop\n");
		lhs = code->operands;
		reg = getreg(WORD);
		sym = lhs->symentry;
		offs = sym->offset - stkframesize;
		asmld(MOVL, offs, reg, lhs->stringval);
		asmfloat(reg, getreg(FLOAT));
		asmsttemp(reg);
		break;
		
	 };
	
  }

void print_iregs(){
	int i = 0; 
	for(; i < NUM_I_REGS; i++){
		printf("%d, ", int_regs[i]);
	}
	printf("\n");
}
  
//unmarks all integer regs. Use at beginning of statement.  
void unmark_iregs(){
	int i;
	for(i = 0; i < NUM_I_REGS; i++)
		int_regs[i] = 0;
}

void unmark_fregs(){
	int i;
	for(i = 0; i < NUM_F_REGS; i++)
		f_regs[i] = 0;
}

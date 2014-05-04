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
void print_fregs();
void process_pointer(TOKEN code);
int process_aref(TOKEN code);

int c_to_jmp[12] = {0, 0, 0, 0, 0, 0, JE, JNE, JL, JLE, JGE, JG};
//0 indicates register unused. EAX, ECX, EDX, EBX
int int_regs[4] = {0, 0, 0, 0};
//0 indicates register unused. xmm0 - xmm15
int f_regs[16] = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};

/* Set DEBUGGEN to 1 for debug printouts of code generation */
#define DEBUGGEN 0

int nextlabel;    /* Next available label number */
int stkframesize;   /* total stack frame size */
int MRR;			//most recent register. Using for aref just for now
int MRR2;
int width;			//0 for word, 1 for float
int rhswidth;		//0 or 1 for the rhs. Using for aref assign
int baseLevel;
int isRHS;	
int rhsTYPE;		//denotes rhs type
int inaref;


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
	if(kind == WORD){
		while(int_regs[index] == 1)
			index++;
		int_regs[index] = 1;
		width = 0;
		return index;
	}
	
	else if(kind == FLOAT){
		while(f_regs[index] == 1)
			index++;
		f_regs[index] = 1;
		width = 1;
		return index + FBASE;
	}
     return RBASE;
  }

/* Trivial version */
/* Generate code for arithmetic expression, return a register number */
int genarith(TOKEN code)
  {   
	int num, reg, reg2, offs, labelnum;	
	int flag = 0;
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
					//printf("processing integer\n");
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
					
				case POINTER:
					num = code->intval;
					reg = getreg(WORD);
					if ( num >= MINIMMEDIATE && num <= MAXIMMEDIATE ){
						asmimmed(MOVQ, num, reg);	
						width = 1;
					}
					break;
			}
			break;
			
		case STRINGTOK:
			labelnum = nextlabel++;
			makeblit(code->stringval, labelnum);
			asmlitarg(labelnum, EDI);
			reg = EDI;
			break;
		
		case IDENTIFIERTOK:
			sym = code->symentry;
			offs = sym->offset - stkframesize;
			//integer
			if(sym->basicdt == 0){
				reg = getreg(WORD);
				asmld(MOVL, offs, reg, code->stringval);
			}
			//real
			else if(sym->basicdt == 1){
				reg = getreg(FLOAT);
				asmld(MOVSD, offs, reg, code->stringval);
			}
			//pointer
			else if(sym->basicdt = 4){
				if(strcmp(code->stringval, "ptr") == 0)
					rhsTYPE = 1;		//float
				else
					rhsTYPE = 0;
				reg = getreg(WORD);
				asmld(MOVQ, offs,  reg, code->stringval);
				width = 1;			//special case
				MRR = reg;									//consider moving all assignemnts to MRR into getreg().
			}
			break;
		case OPERATOR:
			switch(code->whichval){
				case FLOATOP:
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
					lhs = code->operands;
					rhs = lhs->link;
					reg = genarith(lhs);
					reg2 = genarith(rhs);
					//lhs and rhs were both functions that returned a real
					if((reg == FBASE && reg2 == FBASE) || !inaref){
						
						reg = FBASE + 1;		//xmm1
						reg2 = FBASE;			//xmm0
						if(!inaref){
							reg = FBASE;
							reg2 = FBASE + 1;
						}
						asmrr(MULSD, reg2, reg);
					}
					//lhs and rhs were both functions that returned an integer
					else if(reg == RBASE && reg2 == RBASE){
						asmrr(IMULL, reg2, reg);
						
					}
					else if(inaref){
						asmrr(IMULL, reg2, reg);
					}
					break;
					
				case MINUSOP:
					lhs = code->operands;
					rhs = lhs->link;
					reg = genarith(lhs);
					//binary minus
					if(rhs){
						reg2 = genarith(rhs);
						asmrr(SUBL, reg2, reg);
					}
					//unary minus
					else{
						reg2 = getreg(FLOAT);
						asmfneg(reg, reg2);
					}
					//reg is returned after break. Is contents of reg correct.
					break;
					
				case PLUSOP:
					lhs = code->operands;
					rhs = lhs->link;
					reg = genarith(lhs);
					reg2 = genarith(rhs);
					asmrr(ADDL, reg2, reg);
					break;
				
				case LEOP:
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
					reg = reg2;
					break;
				
				case LTOP:
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
					break;
					
				case EQOP:
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
					reg2 = genarith(rhs);
					asmrr(CMPL, reg2, reg);
					reg = reg2;
					break;	
				
				case NEOP:
					lhs = code->operands;
					rhs = lhs->link;
					reg = genarith(lhs);
					reg2 = genarith(rhs);
					asmrr(CMPQ, reg2, reg);
					reg = reg2;
					break;
					
				case FUNCALLOP:
					1 == 1;		//can't have these assignments right after label. doing this for now
					int return_type = code->symentry->datatype->basicdt;
					int args_type = code->symentry->datatype->link->datatype->basicdt;
					//see if xmm0 should be saved
					if(f_regs[0] == 1 && args_type == 1){
						asmsttemp(FBASE);		//store xmm0 onto stack
						flag = 1;
						f_regs[0] = 0;			//mark unused
					}
					unmark_iregs();
					unmark_fregs();
					reg = genarith(code->operands->link);					//function parameters
					//integer arguments go into edi
					if(reg == RBASE)
						asmrr(MOVL, RBASE, EDI);
						
					asmcall(code->symentry->namestring);
					if(return_type == 0){
						reg = RBASE;
						int_regs[EAX] = 1;
					}
					else if(return_type == 1){
						reg = FBASE;
					}
					//restore xmm0 from stack into xmm1. xmm0 holds this instances return value from a function
					if(flag == 1){
						asmldtemp(FBASE + 1);
						f_regs[FBASE + 1] = 1;
					}
					
					break;
					
				case AREFOP:
					inaref = 1;
					//argument to aref is a pointer (id)
					if(code->operands->tokentype == 3){
						reg = genarith(code->operands->link);
						asmop(CLTQ);
						offs = stkframesize - code->operands->symentry->offset;
						if(MRR >= FBASE)
							asmstrr(MOVSD, MRR, -offs, reg, "CHANGE"); 
						else if(MRR < FBASE)
							asmstrr(MOVL, MRR, -offs, reg, "CHANGE");
					}
					//normal aref
					else{
						baseLevel++;
						lhs = code->operands->operands;				//will be a pointer or another aref
						reg = genarith(lhs);
						baseLevel--;
						if(MRR2 < FBASE && baseLevel == 0){
							if(rhswidth == 0){
								if(isRHS == 1){
									int temp_reg = getreg(WORD);
									if(rhsTYPE == 0)
										asmldr(MOVL, code->operands->link->intval, MRR, temp_reg, "^.");
									else
										asmldr(MOVQ, code->operands->link->intval, MRR, temp_reg, "^.");
									int_regs[MRR] = 0;	//mark unused
									MRR = temp_reg;
								}
								else{
									asmstr(MOVL, MRR2, code->operands->link->intval, reg, code->operands->operands->stringval);
									MRR = MRR2;
									
								}
							}
							else if(rhswidth == 1){
								if(isRHS == 1){
									reg = getreg(WORD);
									asmldr(MOVL, code->operands->link->intval, MRR, reg, "^.");
									int_regs[MRR] = 0;		//mark unused
									MRR = reg;
								}
								else{
									asmstr(MOVQ, MRR2, code->operands->link->intval, reg, code->operands->operands->stringval);
									MRR = MRR2;
								}
							}
						}
						else if(MRR2 >= FBASE && baseLevel == 0){
							if(isRHS == 1){
								asmldr(MOVSD, code->operands->link->intval, reg, MRR2, "^.");
								int_regs[reg] = 0;		//mark unused
								MRR = MRR2;
							}
							else{
								asmstr(MOVSD, MRR2, code->operands->link->intval, reg, "^.");
								MRR = MRR2;
							}
						}
						//process intermediate nested aref steps
						if(baseLevel != 0){
							int temp_reg = getreg(WORD);
							int_regs[MRR] = 0;		//mark old register unused
							asmldr(MOVQ, code->operands->link->intval, MRR, temp_reg, "^.");
							//modify MRR here
							MRR = temp_reg;
						}
					}
					inaref = 0;
					break;
			};
	};
	return reg;
}


/* Generate code for a Statement from an intermediate-code form */
void genc(TOKEN code)
  {  TOKEN tok, lhs, rhs;
	TOKEN then_tok, else_tok;
     int reg, reg2, offs;
     SYMBOL sym;
	 inaref = 0;
     if (DEBUGGEN)
       { printf("genc\n");
	 dbugprinttok(code);
       };
     if ( code->tokentype != OPERATOR )
        { printf("Bad code token");
	  dbugprinttok(code);
	};
	
	unmark_iregs();
	unmark_fregs();
	
     switch ( code->whichval )
       { case PROGNOP:
	   tok = code->operands;
	   //special case where progn is on one line. End in graph1.sample
	   if(tok == NULL)
			tok = code->link;
	   while ( tok != NULL )
	     {  genc(tok);
		tok = tok->link;
	      };
	   break;
	 case ASSIGNOP:                   /* Trivial version: handles I := e */
	   lhs = code->operands;
	   rhs = lhs->link;
	   isRHS = 1;
	   reg = genarith(rhs);              /* generate rhs into a register */
	   isRHS = 0;
	   MRR2 = reg;
	   //if lhs is a pointer. (change this so it works recursively). move stuff to process in genarith
		if(lhs->datatype == 4)
			process_pointer(lhs);
		//if it's an aref. (change this so it works recursively). move stuff to process in genarith
		else if(lhs->tokentype == 0 && lhs->whichval == 25){
			//printf("width: %d\n", width);
			rhswidth = width;					//use this value for assignment in aref
			baseLevel = 0;
			reg2 = genarith(lhs);
		}
		
		sym = lhs->symentry;              /* assumes lhs is a simple var  */
		//assuming here that null sym means aref
		if(sym){
	   		offs = sym->offset - stkframesize; /* net offset of the var   */

	       	switch (code->datatype)            /* store value into lhs  */
	         { case INTEGER:
	             asmst(MOVL, reg, offs, lhs->stringval);
	             break;
	             /* ...  */
				case REAL:
					asmst(MOVSD, reg, offs, lhs->stringval);
					break;
	         };
     	}
       break;

	   
	case LABELOP:
		asmlabel(code->operands->intval);
		break;
	
	case IFOP:
		//moves args to registers and generates cmp instruction. JMP uses condition code set by compare
		then_tok = code->operands->link;
		
		else_tok = code->operands->link->link;
		then_tok->link = NULL;						//null out so only this statement is processed
		genarith(code->operands);			
		int op = code->operands->whichval;
		int thenlabel = nextlabel++;
		int elselabel = nextlabel++;
		asmjump(c_to_jmp[op], thenlabel);
		if(else_tok)
			genc(else_tok);
		asmjump(JMP, elselabel);
		//then label
		asmlabel(thenlabel);
		genc(then_tok);
		//else label
		asmlabel(elselabel);
		break;
		
	case FUNCALLOP:
		1 == 1;
		SYMBOL sym = code->operands->symentry;
		int flag = 0;
		if(strcmp("writelnf", code->operands->stringval) == 0){
			flag = 1;
			MRR2 = FBASE;
		}
		isRHS = 1;
		reg = genarith(code->operands->link);					//function parameters
		isRHS = 0;
		if(reg != EDI && !flag)
			asmrr(MOVL, reg, EDI);
		asmcall(code->symentry->namestring);
		break;

	case GOTOOP:
		asmjump(JMP, code->operands->intval);
		break;

	 };


	 
	 
	
  }
  
//process aref and returns register that contians aref address. MOVE THIS CODE TO GENARITH
int process_aref(TOKEN code){
	int reg;
	int ref_off = code->operands->operands->symentry->offset;
	int offset = stkframesize - ref_off;
	reg = getreg(WORD);
	asmld(MOVQ, -offset, reg, code->operands->operands->stringval);
	//store relative to most recently acquired register
	asmstr(MOVQ, reg, code->operands->link->intval, reg, code->operands->operands->stringval);
	return reg;
}
  //MOVE THIS CODE TO GENARITH
void process_pointer(TOKEN code){
	int offs;
	offs = -(stkframesize - code->symentry->offset);
	asmst(MOVQ, MRR, offs, code->stringval);
}

void print_iregs(){
	int i = 0; 
	for(; i < NUM_I_REGS; i++){
		printf("%d, ", int_regs[i]);
	}
	printf("\n");
}

void print_fregs(){
	int i = 0; 
	for(; i < NUM_F_REGS; i++){
		printf("%d, ", f_regs[i]);
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

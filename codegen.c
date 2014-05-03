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
    /*     ***** fix this *****   */
     return RBASE;
  }

/* Trivial version */
/* Generate code for arithmetic expression, return a register number */
int genarith(TOKEN code)
  {   
	//printf("code tokentype: %d\n", code->tokentype);
	//printf("code datatype: %d\n", code->datatype);
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
			//printf("processing stringtype\n");
			//printf("d%sd\n", code->stringval);
			labelnum = nextlabel++;
			makeblit(code->stringval, labelnum);
			asmlitarg(labelnum, EDI);
			reg = EDI;
			break;
		
		case IDENTIFIERTOK:
			/*     ***** fix this *****   */
			//printf("processing id\n");
			//printf("%s\n", code->stringval);
			sym = code->symentry;
			//printf("sym basicdt: %d\n", sym->basicdt);
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
				//printf("processing pointer\n");
				//printf("%d\n", offs);
				reg = getreg(WORD);
				asmld(MOVQ, offs,  reg, code->stringval);
				width = 1;			//special case
				MRR = reg;									//consider moving all assignemnts to MRR into getreg().
				//printf("end processing pointer\n");
			}
			break;
		case OPERATOR:
			/*     ***** fix this *****   */
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
					//unmark_iregs();
					//unmark_fregs();
					//printf("process timesop\n");
					lhs = code->operands;
					//printf("%d\n", lhs == NULL);
					rhs = lhs->link;
					//printf("%d\n", rhs == NULL);
					reg = genarith(lhs);
					reg2 = genarith(rhs);
					//lhs and rhs were both functions that returned a real
					if(reg == FBASE && reg2 == FBASE){
						reg = FBASE + 1;		//xmm1
						reg2 = FBASE;			//xmm0
						asmrr(MULSD, reg2, reg);
					}
					//lhs and rhs were both functions that returned an integer
					else if(reg == RBASE && reg2 == RBASE){
						asmrr(IMULL, reg2, reg);
					}
					else{
						asmrr(IMULL, reg2, reg);
					}
					
					
					break;
					
				case MINUSOP:
					//printf("minusop\n");
					//unmark_iregs();
					//unmark_fregs();
					lhs = code->operands;
					rhs = lhs->link;
					reg = genarith(lhs);
					//binary minus
					if(rhs){
						reg2 = genarith(rhs);
						/* finish this !!! */
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
					//printf("processing plusop\n");
					//print_iregs();
					lhs = code->operands;
					rhs = lhs->link;
					
					reg = genarith(lhs);
					//print_iregs();
					reg2 = genarith(rhs);
					//assuming integer
					//printf("%d\n", lhs->datatype);
					//printf("%d\n", rhs->datatype);
					asmrr(ADDL, reg2, reg);
					break;
				
				case LEOP:
					//unmark_iregs();
					//unmark_fregs();
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
					
				case EQOP:
					//printf("processing eqop\n");
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
					//printf("processing not equal\n");
					lhs = code->operands;
					rhs = lhs->link;
					reg = genarith(lhs);
					reg2 = genarith(rhs);
					asmrr(CMPQ, reg2, reg);
					reg = reg2;
					break;
					
				case FUNCALLOP:
					//printf("generating for funcall\n");
					//print_fregs();
					1 == 1;		//can't have these assignments right after label. doing this for now
					int return_type = code->symentry->datatype->basicdt;
					//printf("return type: %d\n", return_type);
					int args_type = code->symentry->datatype->link->datatype->basicdt;
					//printf("args type: %d\n", args_type);
					//see if xmm0 should be saved
					if(f_regs[0] == 1 && args_type == 1){
						asmsttemp(FBASE);		//store xmm0 onto stack
						flag = 1;
						f_regs[0] = 0;			//mark unused
					}
					unmark_iregs();
					unmark_fregs();
					//printf("%s\n", code->symentry->namestring);
					//printf("return type: %d\n", code->symentry->datatype->basicdt);	//return type
					//printf("arguments type: %d\n", code->symentry->datatype->link->datatype->basicdt);	//arguments type
					//printf("%d\n", code->operands->link->tokentype);
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
						//should I set f_reg here?
					}
					
					//restore xmm0 from stack into xmm1. xmm0 holds this instances return value from a function
					if(flag == 1){
						asmldtemp(FBASE + 1);
						f_regs[FBASE + 1] = 1;
					}
					
					break;
					
				case AREFOP:
					
					//printf("processing aref\n");
					//printf("tokentype: %d\n", code->operands->tokentype);
					//printf("%d\n", code->operands->link->intval);
													//first aref in a nest of arefs
					//argument to aref is a pointer (id)
					if(code->operands->tokentype == 3){
						//print_iregs();
						//print_fregs();
						reg = genarith(code->operands->link);
						asmop(CLTQ);
						//need one more instruction here
						printf("another here\n");
					}
					//normal aref
					else{
						baseLevel++;
						lhs = code->operands->operands;				//will be a pointer or another aref
						//printf("%s\n", lhs->stringval);
						/* if(lhs->tokentype == IDENTIFIER && lhs->datatype == POINTER)
							printf("process pointer here\n");
						else if(lhs->datatype =  */
						reg = genarith(lhs);
						baseLevel--;
						//printf("MRR: %d\n", MRR);
						//printf("width: %d\n", width);
						//printf("%d\n", rhswidth);
						
						if(MRR2 < FBASE && baseLevel == 0){
							if(rhswidth == 0){
								if(isRHS == 1){
								
								}
								else{
									asmstr(MOVL, MRR2, code->operands->link->intval, reg, code->operands->operands->stringval);
								}
							}
							else if(rhswidth == 1){
								if(isRHS == 1){
									reg = getreg(WORD);
									asmldr(MOVL, code->operands->link->intval, MRR, reg, "^.");
									int_regs[MRR] = 0;		//mark unused
									
								}
								else{
									asmstr(MOVQ, MRR2, code->operands->link->intval, reg, code->operands->operands->stringval);
								}
								
							}
						}
						else if(MRR2 >= FBASE && baseLevel == 0){
							if(isRHS == 1){
								asmldr(MOVSD, code->operands->link->intval, reg, MRR2, "^.");
								int_regs[reg] = 0;		//mark unused
							}
							else{
								asmstr(MOVSD, MRR2, code->operands->link->intval, reg, "^.");
								
							}
						}
						//process intermediate nested aref steps
						if(baseLevel != 0){
							//printf("intermediate steps\n");
							//printf("MRR: %d\n", MRR);
							int temp_reg = getreg(WORD);
							//printf("%d\n", temp_reg);
							int_regs[MRR] = 0;		//mark old register unused
							
							//printf("%d\n", code->operands->link->intval);
							//hardcoding movq for now. check later
							asmldr(MOVQ, code->operands->link->intval, MRR, temp_reg, "^.");
							//modify MRR here
							MRR = temp_reg;
						}
					}
					
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
	   //printf("processing progn\n");
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
	  // printf("processing assignop\n");
	  //print_iregs();
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
		//genc(code->operands);
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
		//printf("processing funcall\n");
		//printf("tokentype: %d\n", code->operands->link->tokentype);
		reg = genarith(code->operands->link);					//function parameters
		asmcall(code->symentry->namestring);
		break;

	case GOTOOP:
		//printf("processing goto\n");
		asmjump(JMP, code->operands->intval);
		break;

	 };


	 
	 
	
  }
  
//process aref and returns register that contians aref address. MOVE THIS CODE TO GENARITH
int process_aref(TOKEN code){
	int reg;
	// printf("processing aref\n");
	// printf("%d\n", code->operands->link->intval);
	// printf("%d\n", code->operands->operands->symentry->offset);
	int ref_off = code->operands->operands->symentry->offset;
	int offset = stkframesize - ref_off;
	//printf("%d\n", offset);
	reg = getreg(WORD);
	asmld(MOVQ, -offset, reg, code->operands->operands->stringval);
	//store relative to most recently acquired register
	asmstr(MOVQ, reg, code->operands->link->intval, reg, code->operands->operands->stringval);
	return reg;
}
  //MOVE THIS CODE TO GENARITH
void process_pointer(TOKEN code){
	//printf("processing pointer\n");
	int offs;
	offs = -(stkframesize - code->symentry->offset);
	//printf("needed offset: %d\n", stkframesize - code->symentry->offset);
	asmst(MOVQ, RAX, offs, code->stringval);
	
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

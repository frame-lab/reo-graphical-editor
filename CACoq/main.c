#include<stdlib.h>
#include<stdio.h>
#include<string.h>
#include"reo2ca.h"
#include "state.h"


int main(void){
	struct AutomatoList *automatos = NULL;
	FILE *f = fopen("input.txt", "r");
	input2CoqCA(f);
	return 0;

}

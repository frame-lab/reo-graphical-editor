#include<stdlib.h>
#include<stdio.h>
#include<string.h>
#include "state.h"


struct Automato *createSync(char *ports, int nAuto)
{
    char port1[20];
    char port2[20];
    memset(port1, 0, sizeof(port1));
    memset(port2, 0, sizeof(port2));
    int i = 0, j = 0;
    while (ports[i] != ',')
    {
        port1[i] = ports[i];
        i++;
    }
    i++;
    while (ports[i] != ')')
    {
        if (ports[i] != ' ')
        {
            port2[j] = ports[i];
            j++;
        }
        i++;
    }
    struct State *state1 = newState("q0", 1);
    char *condition = (char *)malloc(83 * sizeof(char));
    struct StringList *portsList = NULL;
    portsList = addString(portsList, port1);
    portsList = addString(portsList, port2);
    //snprintf(condition, 600, "ports.%s[time] != NULL & ports.%s[time] = ports.%s[time]", port1, port1, port2);
	snprintf(condition, 83, "ConstraintAutomata.eqDc %s %s ", port1, port2); //erick: ver como isso afeta estados não determinísticos. acho que não afeta. seria melhor preecher o destino na condition?
    struct Transition *transition = (struct Transition *)malloc(sizeof(struct Transition));
    transition->start = state1;
    transition->end = state1;
    transition->nPorts = 2;
    transition->ports = portsList;
    transition->condition = condition;
    transition->blocked = 0;
    addTransition(transition);
    char *automatoName = (char *)malloc(600 * sizeof(char));
    snprintf(automatoName, 600, "sync%d", nAuto);
    struct Automato *automato = newAutomato(automatoName);
    addState(state1, automato);
    return automato;
}

struct Automato *createLossy(char *ports, int nAuto)
{
    char port1[20];
    char port2[20];
    memset(port1, 0, sizeof(port1));
    memset(port2, 0, sizeof(port2));
    int i = 0, j = 0;
    while (ports[i] != ',')
    {
        port1[i] = ports[i];
        i++;
    }
    i++;
    while (ports[i] != ')')
    {
        if (ports[i] != ' ')
        {
            port2[j] = ports[i];
            j++;
        }
        i++;
    }
    struct State *state1 = newState("q0", 1);
    char *condition = (char *)malloc(600 * sizeof(char));
    struct StringList *portsList = NULL;
    portsList = addString(portsList, port1);
    portsList = addString(portsList, port2);
	snprintf(condition, 83, "ConstraintAutomata.eqDc %s %s", port1, port2);
    struct Transition *transition = (struct Transition *)malloc(sizeof(struct Transition));
    transition->start = state1;
    transition->end = state1;
    transition->nPorts = 2;
    transition->ports = portsList;
    transition->condition = condition;
    transition->blocked = 0;
    addTransition(transition);
    condition = (char *)malloc(600 * sizeof(char));
    portsList = NULL;
    portsList = addString(portsList, port1);
    snprintf(condition, 600, "ConstraintAutomata.tDc"); //erick: ao recuperar esse cara, escrever o tipo esperado pelo tDc.
    transition = (struct Transition *)malloc(sizeof(struct Transition));
    transition->start = state1;
    transition->end = state1;
    transition->ports = portsList;
    transition->condition = condition;
    transition->blocked = 0;
    addTransition(transition);
    char *automatoName = (char *)malloc(600 * sizeof(char));
    snprintf(automatoName, 600, "lossySync%d", nAuto);
    struct Automato *automato = newAutomato(automatoName);
    addState(state1, automato);
    return automato;
}

struct Automato *createFifo(char *ports, int nAuto)
{
    char port1[20];
    char port2[20];
    memset(port1, 0, sizeof(port1));
    memset(port2, 0, sizeof(port2));
    int i = 0, j = 0;
    while (ports[i] != ',')
    {
        port1[i] = ports[i];
        i++;
    }
    i++;
    while (ports[i] != ')')
    {
        if (ports[i] != ' ')
        {
            port2[j] = ports[i];
            j++;
        }
        i++;
    }
    struct State *state1 = newState("q0", 1);
    struct State *state2 = newState("p0", 0);
    struct State *state3 = newState("p1", 0);
    char *condition = (char *)malloc(600 * sizeof(char));
    struct StringList *portsList = NULL;
    portsList = addString(portsList, port1);
    snprintf(condition, 100, "ConstraintAutomata.dc %s = (Some 0)", port1); //erick: parei aqui na tradução
    struct Transition *transition = (struct Transition *)malloc(sizeof(struct Transition));
    transition->start = state1;
    transition->end = state2;
    transition->nPorts = 1;
    transition->ports = portsList;
    transition->condition = condition;
    transition->blocked = 0;
    addTransition(transition);
    condition = (char *)malloc(600 * sizeof(char));
    portsList = NULL;
    portsList = addString(portsList, port1);
    snprintf(condition, 100, "ConstraintAutomata.dc %s = (Some 1)", port1);
    transition = (struct Transition *)malloc(sizeof(struct Transition));
    transition->start = state1;
    transition->end = state3;
    transition->nPorts = 1;
    transition->ports = portsList;
    transition->condition = condition;
    transition->blocked = 0;
    addTransition(transition);
    condition = (char *)malloc(600 * sizeof(char));
    portsList = NULL;
    portsList = addString(portsList, port2);
    snprintf(condition, 83, "ConstraintAutomata.dc %s = (Some 1)", port2);
    transition = (struct Transition *)malloc(sizeof(struct Transition));
    transition->start = state3;
    transition->end = state1;
    transition->nPorts = 1;
    transition->ports = portsList;
    transition->condition = condition;
    transition->blocked = 0;
    addTransition(transition);
    condition = (char *)malloc(600 * sizeof(char));
    portsList = NULL;
    portsList = addString(portsList, port2);
    snprintf(condition, 600, "ConstraintAutomata.dc %s = (Some 0)", port2);
    transition = (struct Transition *)malloc(sizeof(struct Transition));
    transition->start = state2;
    transition->end = state1;
    transition->nPorts = 1;
    transition->ports = portsList;
    transition->condition = condition;
    transition->blocked = 0;
    addTransition(transition);
    char *automatoName = (char *)malloc(600 * sizeof(char));
    snprintf(automatoName, 600, "fifo%d", nAuto);
    struct Automato *automato = newAutomato(automatoName);
    addState(state1, automato);
    addState(state2, automato);
    addState(state3, automato);
    return automato;
}

struct Automato *createSyncDrain(char *ports, int nAuto)
{
    char port1[20];
    char port2[20];
    memset(port1, 0, sizeof(port1));
    memset(port2, 0, sizeof(port2));
    int i = 0, j = 0;
    while (ports[i] != ',')
    {
        port1[i] = ports[i];
        i++;
    }
    i++;
    while (ports[i] != ')')
    {
        if (ports[i] != ' ')
        {
            port2[j] = ports[i];
            j++;
        }
        i++;
    }
    struct State *state1 = newState("q0", 1);
    char *condition = (char *)malloc(600 * sizeof(char));
    struct StringList *portsList = NULL;
    portsList = addString(portsList, port1);
    portsList = addString(portsList, port2);
    snprintf(condition, 600, "ConstraintAutomata.tDc");
    struct Transition *transition = (struct Transition *)malloc(sizeof(struct Transition));
    transition->start = state1;
    transition->end = state1;
    transition->nPorts = 1;
    transition->ports = portsList;
    transition->condition = condition;
    transition->blocked = 0;
    addTransition(transition);
    char *automatoName = (char *)malloc(600 * sizeof(char));
    snprintf(automatoName, 600, "syncDrain%d", nAuto);
    struct Automato *automato = newAutomato(automatoName);
    addState(state1, automato);
    return automato;
}

struct Automato *createAsync(char *ports, int nAuto)
{
    char port1[20];
    char port2[20];
    memset(port1, 0, sizeof(port1));
    memset(port2, 0, sizeof(port2));
    int i = 0, j = 0;
    while (ports[i] != ',')
    {
        port1[i] = ports[i];
        i++;
    }
    i++;
    while (ports[i] != ')')
    {
        if (ports[i] != ' ')
        {
            port2[j] = ports[i];
            j++;
        }
        i++;
    }
    struct State *state1 = newState("q0", 1);
    char *condition = (char *)malloc(600 * sizeof(char));
    struct StringList *portsList = NULL;
    portsList = addString(portsList, port1);
    snprintf(condition, 600, "ConstraintAutomata.tDc");
    struct Transition *transition = (struct Transition *)malloc(sizeof(struct Transition));
    transition->start = state1;
    transition->end = state1;
    transition->nPorts = 1;
    transition->ports = portsList;
    transition->condition = condition;
    transition->blocked = 0;
    addTransition(transition);
    condition = (char *)malloc(600 * sizeof(char));
    portsList = NULL;
    portsList = addString(portsList, port2);
    snprintf(condition, 600, "ConstraintAutomata.tDc");
    transition = (struct Transition *)malloc(sizeof(struct Transition));
    transition->start = state1;
    transition->end = state1;
    transition->nPorts = 1;
    transition->ports = portsList;
    transition->condition = condition;
    transition->blocked = 0;
    addTransition(transition);
    char *automatoName = (char *)malloc(600 * sizeof(char));
    snprintf(automatoName, 600, "asyncDrain%d", nAuto);
    struct Automato *automato = newAutomato(automatoName);
    addState(state1, automato);
    return automato;
}

struct Automato *createMerger(char *ports, int nAuto)
{
    char port1[20];
    char port2[20];
    char port3[20];
    memset(port1, 0, sizeof(port1));
    memset(port2, 0, sizeof(port2));
    memset(port3, 0, sizeof(port3));
    int i = 0, j = 0;
    while (ports[i] != ',')
    {
        port1[i] = ports[i];
        i++;
    }
    i++;
    while (ports[i] != ')')
    {
        if (ports[i] != ' ')
        {
            port2[j] = ports[i];
            j++;
        }
        i++;
    }
    i++;
    j = 0;
    while (ports[i] != ')')
    {
        if (ports[i] != ' ')
        {
            port3[j] = ports[i];
            j++;
        }
        i++;
    }
    struct State *state1 = newState("q0", 1);
    char *condition = (char *)malloc(600 * sizeof(char));
    struct StringList *portsList = NULL;
    portsList = addString(portsList, port1);
    portsList = addString(portsList, port3);
    snprintf(condition, 600, "ports.%s[time] != NULL & ports.%s[time] = ports.%s[time]", port3, port1, port3);
    struct Transition *transition = (struct Transition *)malloc(sizeof(struct Transition));
    transition->start = state1;
    transition->end = state1;
    transition->nPorts = 2;
    transition->ports = portsList;
    transition->condition = condition;
    transition->blocked = 0;
    addTransition(transition);
    condition = (char *)malloc(600 * sizeof(char));
    portsList = NULL;
    portsList = addString(portsList, port2);
    portsList = addString(portsList, port3);
    snprintf(condition, 600, "ports.%s[time] != NULL & ports.%s[time] = ports.%s[time]", port3, port2, port3);
    transition = (struct Transition *)malloc(sizeof(struct Transition));
    transition->start = state1;
    transition->end = state1;
    transition->nPorts = 2;
    transition->ports = portsList;
    transition->condition = condition;
    transition->blocked = 0;
    addTransition(transition);
    char *automatoName = (char *)malloc(600 * sizeof(char));
    snprintf(automatoName, 600, "merger%d", nAuto);
    struct Automato *automato = newAutomato(automatoName);
    addState(state1, automato);
    return automato;
}

struct Automato *createReplicator(char *ports, int nAuto)
{
    char port1[20];
    char port2[20];
    char port3[20];
    memset(port1, 0, sizeof(port1));
    memset(port2, 0, sizeof(port2));
    memset(port3, 0, sizeof(port3));
    int i = 0, j = 0;
    while (ports[i] != ',')
    {
        port1[i] = ports[i];
        i++;
    }
    i++;
    while (ports[i] != ')')
    {
        if (ports[i] != ' ')
        {
            port2[j] = ports[i];
            j++;
        }
        i++;
    }
    i++;
    j = 0;
    while (ports[i] != ')')
    {
        if (ports[i] != ' ')
        {
            port3[j] = ports[i];
            j++;
        }
        i++;
    }
    struct State *state1 = newState("q0", 1);
    char *condition = (char *)malloc(600 * sizeof(char));
    struct StringList *portsList = NULL;
    portsList = addString(portsList, port1);
    portsList = addString(portsList, port2);
    portsList = addString(portsList, port3);
    snprintf(condition, 600, "ports.%s[time] != NULL & ports.%s[time] = ports.%s[time] & ports.%s[time] = ports.%s[time]", port1, port1, port2, port1, port3);
    struct Transition *transition = (struct Transition *)malloc(sizeof(struct Transition));
    transition->start = state1;
    transition->end = state1;
    transition->nPorts = 3;
    transition->ports = portsList;
    transition->condition = condition;
    transition->blocked = 0;
    addTransition(transition);
    char *automatoName = (char *)malloc(600 * sizeof(char));
    snprintf(automatoName, 600, "replicator%d", nAuto);
    struct Automato *automato = newAutomato(automatoName);
    addState(state1, automato);
    return automato;
}

struct Automato *createFilter(char *ports, int nAuto)
{
    char port1[20];
    char port2[20];
    memset(port1, 0, sizeof(port1));
    memset(port2, 0, sizeof(port2));
    int i = 0, j = 0;
    while (ports[i] != ',')
    {
        port1[i] = ports[i];
        i++;
    }
    i++;
    while (ports[i] != ')')
    {
        if (ports[i] != ' ')
        {
            port2[j] = ports[i];
            j++;
        }
        i++;
    }
    struct State *state1 = newState("q0", 1);
    char *condition = (char *)malloc(600 * sizeof(char));
    struct StringList *portsList = NULL;
    portsList = addString(portsList, port1);
    snprintf(condition, 600, "ports.%s[time] != NULL & TRUE", port1);
    struct Transition *transition = (struct Transition *)malloc(sizeof(struct Transition));
    transition->start = state1;
    transition->end = state1;
    transition->nPorts = 1;
    transition->ports = portsList;
    transition->condition = condition;
    transition->blocked = 0;
    addTransition(transition);
    condition = (char *)malloc(600 * sizeof(char));
    portsList = NULL;
    portsList = addString(portsList, port1);
    portsList = addString(portsList, port2);
    snprintf(condition, 600, "ports.%s[time] != NULL & ports.%s[time] = ports.%s[time] & TRUE", port1, port1, port2);
    transition = (struct Transition *)malloc(sizeof(struct Transition));
    transition->start = state1;
    transition->end = state1;
    transition->nPorts = 2;
    transition->ports = portsList;
    transition->condition = condition;
    transition->blocked = 0;
    addTransition(transition);
    char *automatoName = (char *)malloc(600 * sizeof(char));
    snprintf(automatoName, 600, "filter%d", nAuto);
    struct Automato *automato = newAutomato(automatoName);
    addState(state1, automato);
    return automato;
}

struct Automato *createTransformer(char *ports, int nAuto)
{
    char port1[20];
    char port2[20];
    memset(port1, 0, sizeof(port1));
    memset(port2, 0, sizeof(port2));
    int i = 0, j = 0;
    while (ports[i] != ',')
    {
        port1[i] = ports[i];
        i++;
    }
    i++;
    while (ports[i] != ')')
    {
        if (ports[i] != ' ')
        {
            port2[j] = ports[i];
            j++;
        }
        i++;
    }
    struct State *state1 = newState("q0", 1);
    char *condition = (char *)malloc(600 * sizeof(char));
    struct StringList *portsList = NULL;
    portsList = addString(portsList, port1);
    portsList = addString(portsList, port2);
    snprintf(condition, 600, "ports.%s[time] != NULL & TRUE", port1);
    struct Transition *transition = (struct Transition *)malloc(sizeof(struct Transition));
    transition->start = state1;
    transition->end = state1;
    transition->nPorts = 1;
    transition->ports = portsList;
    transition->condition = condition;
    transition->blocked = 0;
    addTransition(transition);
    char *automatoName = (char *)malloc(600 * sizeof(char));
    snprintf(automatoName, 600, "transformer%d", nAuto);
    struct Automato *automato = newAutomato(automatoName);
    addState(state1, automato);
    return automato;
}

struct AutomatoList *
readInput(FILE *f)
{
    struct AutomatoList *automatoList = NULL;
    struct Automato *temp = NULL;
    char line[1024];
    char command[1024];
    char ports[1024];
    int i = 0;
    int j = 0;
    int nAuto = 0;
    memset(line, '\0', sizeof(line));
    while (fgets(line, sizeof line, f) != NULL)
    {
        i = 0;
        j = 0;
        memset(command, '\0', sizeof(command));
        memset(ports, '\0', sizeof(ports));
        while (line[i] != '(' && line[i] != '\n' && line[i] != '\0' && line[i] != '/')
        {
            if (line[i] != '\t')
            {
                command[j] = line[i];
                j++;
            }
            i++;
        }
        i++;
        j = 0;
        while ((line[i] != '\n') && (line[i] != '\0') && line[i] != '/')
        {
            ports[j] = line[i];
            i++;
            j++;
        }
	printf("%s",line);
        if (strcmp(command, "sync") == 0)
        {
            nAuto++;
            temp = createSync(ports, nAuto);
            automatoList = addAutomato(automatoList, temp);
        }
        if (strcmp(command, "lossysync") == 0)
        {
            nAuto++;
            temp = createLossy(ports, nAuto);
            automatoList = addAutomato(automatoList, temp);
        }
        if (strcmp(command, "fifo1") == 0)
        {
            nAuto++;
            temp = createFifo(ports, nAuto);
            automatoList = addAutomato(automatoList, temp);
        }
        if (strcmp(command, "syncdrain") == 0)
        {
            nAuto++;
            temp = createSyncDrain(ports, nAuto);
            automatoList = addAutomato(automatoList, temp);
        }
        if (strcmp(command, "syncspout") == 0)
        {
            nAuto++;
            temp = createAsync(ports, nAuto);
            automatoList = addAutomato(automatoList, temp);
        }
        if (strcmp(command, "merger") == 0)
        {
            nAuto++;
            temp = createMerger(ports, nAuto);
            automatoList = addAutomato(automatoList, temp);
        }
        if (strcmp(command, "replicator") == 0)
        {
            nAuto++;
            temp = createReplicator(ports, nAuto);
            automatoList = addAutomato(automatoList, temp);
        }
        if (strcmp(command, "filter") == 0)
        {
            nAuto++;
            temp = createFilter(ports, nAuto);
            automatoList = addAutomato(automatoList, temp);
        }
        if (strcmp(command, "transformer") == 0)
        {
            nAuto++;
            temp = createTransformer(ports, nAuto);
            automatoList = addAutomato(automatoList, temp);
        }
        memset(line, '\0', sizeof(line));
    }
    return automatoList;
}
int isItIn(struct StringList *list, char *string){
	if(!list) return 0;
	while(list){
		if(!strcmp(list->string,string)) return 1;
		list = list -> nextString;
	}
	return 0;
}

void freeAuxStringList(struct StringList *l){
	if (l->nextString){
		freeAuxStringList(l->nextString);
		free(l->string);
		free(l);
	}

}

void input2CoqCAHs(FILE *f) {
    struct AutomatoList *automatoList = readInput(f);
	struct StringList *resultingPorts = NULL;
	//controls states that have been declared
	struct StringList *resultingStates = NULL;
	struct StringList *currStates;
	int k = 0;
	//printf("%s", automatoList[0].automato->ports->string);
    //struct Automato *temp = NULL;
    char line[1024];
    char command[1024];
	char transitionRelName[69];
	char automatonName[81];

	//Coq datatype for data items
	char dataDomain[81] = "nat";

    int i = 0;
    int j = 0;
    int nAuto = 0;
    memset(line, '\0', sizeof(line));

	FILE *output = fopen("coqModel.v","w");

	fprintf(output,"(* File generated by ReoXplore graphical interface *) \n");
	fprintf(output,"(* It requires the compilation of CaMain.v file in https://github.com/frame-lab/CACoq. *) \n");
    fprintf(output,"Require Import CAMain. \n");
	struct AutomatoList *automatonPorts = automatoList;
	//automaton's name
	strcpy(automatonName,automatonPorts-> automato -> name);
	while(automatonPorts){
		//erick: para portas parece melhor colocar em um tipo único.
		//currPorts = NULL;
		struct StringList * singlePort = automatonPorts->automato->ports;
		while(singlePort){
			if(!isItIn(resultingPorts,singlePort->string))//{
				resultingPorts = addString(resultingPorts, singlePort->string);
			//	currPorts = addString(currPorts,singlePort->string);
			//}
			printf("%s",singlePort->string);
			singlePort = singlePort->nextString;
		}
		automatonPorts = automatonPorts->nextAutomato;
	
	}	
		fprintf(output,"Inductive modelPortsType := \n");
		//erick: botar portas em maiusculo?
		struct StringList * coqPorts = resultingPorts;
		fprintf(output,"\t");
		while(coqPorts -> nextString){
			fprintf(output, "%s | ",coqPorts->string);
			coqPorts = coqPorts->nextString;
		}
		fprintf(output, " %s. \n",coqPorts->string);

		//proof of equality between ports:
		fprintf(output,"Instance modelPortsEqDec : EqDec modelPortsType eq :=\n");
		fprintf(output,"\t{equiv_dec x y := \n");
		fprintf(output,"\t\t match x, y with \n");
		coqPorts = resultingPorts;
		while(coqPorts){
			struct StringList * nextp = resultingPorts;
				while(nextp){
				if(!strcmp(coqPorts->string,nextp->string))
					fprintf(output,"\t\t| %s , %s => in_left \n",coqPorts->string,coqPorts->string);
				else
					fprintf(output,"\t\t| %s , %s => in_right\n",coqPorts->string,nextp->string);
				nextp = nextp -> nextString;
			}
			coqPorts = coqPorts -> nextString;
		}
		fprintf(output,"\tend\n");
		fprintf(output,"\t}.\n");
		printf("Proof.\nall: congruence.\n");

		//free aux var
		//freeAuxStringList(currPorts);
		//automatonPorts = automatonPorts->nextAutomato;
	
	//}	
	//states type
	struct AutomatoList *automatonStates = automatoList;
	while(automatonStates){
		currStates = NULL;
		struct StateList * singleState = automatonStates->automato->states;
		while(singleState){
			if(isItIn(resultingStates, singleState->state->name)){
				singleState->state->name[0]++; //erick: p diferenciar os estados. conferir como isso afeta os estados resultantes
				while(isItIn(resultingStates, singleState->state->name)) singleState->state->name[0]++; //na hora de incremetar tem que ver se já existe
				
			}
			currStates = addString(currStates,singleState->state->name);
			resultingStates = addString(resultingStates, singleState->state->name);
			singleState = singleState->nextState;
		}
		fprintf(output,"Inductive %sStatesType := \n",automatonStates->automato->name);
		struct StringList * coqStates = currStates;
		while(coqStates -> nextString){
			fprintf(output, "\t %s | ",coqStates->string);
			coqStates = coqStates->nextString;
		}
		fprintf(output, "\t%s.\n",coqStates->string);

		//proof of equality between states:
		fprintf(output,"Instance %sEqDec : EqDec %sStatesType eq :=\n",automatonStates->automato->name,automatonStates->automato->name);
		fprintf(output,"\t{equiv_dec x y := \n");
		fprintf(output,"\t\t match x, y with \n");
		coqStates = currStates;
		while(coqStates){
			struct StringList * nextp = currStates;
			while(nextp){
				if(!strcmp(coqStates->string,nextp -> string))
					fprintf(output,"\t\t| %s , %s => in_left \n",coqStates->string,nextp->string);
				else					
					fprintf(output,"\t\t| %s , %s => in_right \n",coqStates->string,nextp->string);
				nextp = nextp -> nextString;
			}
			coqStates = coqStates -> nextString;
		}
		fprintf(output,"\tend\n");
		fprintf(output,"\t}.\n");
		printf("Proof.\nall: congruence.\n");
		
		freeAuxStringList(currStates);

		automatonStates = automatonStates->nextAutomato;
	}
	//automaton construction:
	struct AutomatoList * modelAutomata = automatoList;
	//transitions definition
	while(modelAutomata){
		struct StateList *automatonStates = modelAutomata->automato->states;
		//implicit argument (caso explicit nao de cert)
		strcpy(transitionRelName,modelAutomata->automato->name);
		strcat(transitionRelName,"rel");
		fprintf(output,"Definition %srel (s: %sStatesType) :=\n",modelAutomata->automato->name,modelAutomata->automato->name);
		fprintf(output,"\tmatch s with :=\n");
		//single state transitions
		while(automatonStates -> nextState){
			struct State *currentState = automatonStates->state;
			struct Transition *currentTrans;
			//printf("%s", modelAutomata->automato->states->state->transitions->transition->condition);
			fprintf(output,"\t\t | %s => [", currentState->name);
			struct TransitionList *transitionsForCurrentState = currentState->transitions;
			while (transitionsForCurrentState -> nextTransition){
				struct Transition *currentTrans = transitionsForCurrentState->transition;
				fprintf(output,"([");
				struct StringList *ports = currentTrans->ports;
				while (ports->nextString){
					fprintf(output,"%s;",ports ->string);
					ports = ports->nextString;				
				}
				fprintf(output,"%s",ports ->string);
				char *cond = currentTrans->condition;
				//erick:tratamento pro tipo dc:
				if (strstr(cond,"tDc")){
					strcat(cond," modelPortsEqDec ");
					strcat(cond, dataDomain);
				}
				fprintf(output,"], %s", cond);//erick:traduzir condições pra coq. posso fazer isso diretamente nas funções la em cima.
				fprintf(output, " [%s]); ", currentTrans->end->name);
				transitionsForCurrentState = transitionsForCurrentState -> nextTransition;
			}
			//last transition for a single state
			currentTrans = transitionsForCurrentState->transition;
			printf("%s",currentTrans->condition);
			fprintf(output,"([");
			struct StringList *ports = currentTrans->ports;
			while (ports -> nextString){
				fprintf(output,"%s;",ports ->string);
				ports = ports->nextString;				
			}
			fprintf(output,"%s",ports ->string);
			char *cond = currentTrans->condition;
			//erick:tratamento pro tipo dc:
			if (strstr(cond,"tDc")){
				strcat(cond," modelPortsEqDec ");
				strcat(cond, dataDomain);
			}
			fprintf(output,"], %s", cond);//erick:traduzir condições pra coq. posso fazer isso diretamente nas funções la em cima.
			fprintf(output, " [%s])] \n", currentTrans->end->name);
			automatonStates = automatonStates->nextState;
		}
		//last transition
		struct State *currentState = automatonStates->state;
		//printf("%s", modelAutomata->automato->states->state->transitions->transition->condition);
		struct Transition *currentTrans;
		fprintf(output,"\t\t | %s => [", currentState->name);
		struct TransitionList *transitionsForCurrentState = currentState->transitions;
		while (transitionsForCurrentState -> nextTransition){
			struct Transition * currentTrans = transitionsForCurrentState->transition;
			fprintf(output,"([");
			struct StringList *ports = currentTrans->ports;
			while (ports->nextString){
				fprintf(output,"%s;",ports ->string);
				ports = ports->nextString;				
			}
			fprintf(output,"%s",ports ->string);
			char *cond = currentTrans->condition;
			if (strstr(cond,"tDc")){
					strcat(cond," modelPortsEqDec ");
					strcat(cond,dataDomain);
			}
			fprintf(output,"], %s", cond);//erick:traduzir condições pra coq. posso fazer isso diretamente nas funções la em cima.
			fprintf(output, " [%s])];", currentTrans->end->name);
			transitionsForCurrentState = transitionsForCurrentState -> nextTransition;
		}	
		currentTrans = transitionsForCurrentState->transition;
		printf("%s",currentTrans->condition);
		fprintf(output,"([");
		struct StringList *ports = currentTrans->ports;
		while (ports -> nextString){
			fprintf(output,"%s;",ports ->string);
			ports = ports->nextString;				
		}
		fprintf(output,"%s",ports ->string);
		char *cond = currentTrans->condition;
		//erick:tratamento pro tipo dc:
		if (strstr(cond,"tDc")){
			strcat(cond," modelPortsEqDec ");
			strcat(cond, dataDomain);
		}
		fprintf(output,"], %s", cond);//erick:traduzir condições pra coq. posso fazer isso diretamente nas funções la em cima.
		fprintf(output, " [%s])] \n", currentTrans->end->name);
		fprintf(output,"\tend.\n");

		//automaton definition
		fprintf(output, "Definition %sAutomaton := {| \n",modelAutomata->automato->name);
		//automaton's states
		fprintf(output,"\tConstraintAutomata.Q := [");		
		struct StateList * initialState = modelAutomata->automato->states;
		while(initialState->nextState){
			fprintf(output,"%s;",initialState->state->name);
			initialState = initialState->nextState;
		}
		fprintf(output,"%s",initialState->state->name);
		initialState = initialState->nextState;
		fprintf(output,"];\n");
		//automaton's ports
		fprintf(output,"\tConstraintAutomata.N := [");		
		struct StringList * automatonPorts = modelAutomata->automato->ports;
		while(automatonPorts ->nextString){
			fprintf(output,"%s;",automatonPorts->string);
			automatonPorts = automatonPorts->nextString;
		}
		//last automaton's ports
		fprintf(output,"%s];\n",automatonPorts->string);
		//automaton's relation in Coq
		fprintf(output,"\tConstraintAutomata.T := %s\n",transitionRelName);
		//who are the initial states?
		fprintf(output,"\tConstraintAutomata.Q0 := [");
	    initialState = modelAutomata->automato->states;
		while(initialState->nextState){
			if(initialState->state->init)fprintf(output,"%s",initialState->state->name);
 			initialState = initialState->nextState;
		}
		//last initial state
		if(initialState->state->init)fprintf(output,"%s",initialState->state->name);
		fprintf(output,"]\n");
		fprintf(output,"|}\n");

		//next automaton
		modelAutomata = modelAutomata -> nextAutomato;
	}

	//product definition
	modelAutomata = automatoList;
	struct AutomatoList * nextAutomaton = modelAutomata->nextAutomato;
	char lastProductName[81];
	char currProductName[81];
	//at least two automata: first product:
	if(nextAutomaton){
		strcpy(lastProductName,modelAutomata->automato->name);
		strcat(lastProductName,nextAutomaton->automato->name);
		//product must be done using two automata at a time.
		fprintf(output,"Definition %sProduct := ProductAutomata.buildPA %sAutomaton %sAutomaton.\n",lastProductName,modelAutomata->automato->name,nextAutomaton->automato->name);
		nextAutomaton = nextAutomaton->nextAutomato;
	}
	while(nextAutomaton){
		strcpy(currProductName,modelAutomata->automato->name);
		strcat(currProductName,nextAutomaton->automato->name);
		fprintf(output,"Definition %sProduct := ProductAutomata.buildPA %sProduct %sAutomaton.\n",currProductName,lastProductName,nextAutomaton->automato->name);
		nextAutomaton = nextAutomaton ->nextAutomato;
	}
	fprintf(output,"Require Extraction.");
	fprintf(output,"Extraction \"haskellModel\" %s.",currProductName); 
	fclose(output);
}




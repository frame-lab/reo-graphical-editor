#include <stdio.h>
#include <stdlib.h>
#include "headers/state.h"
#include "headers/caToNuXmv.h"
#include "headers/input.h"

int main(void)
{
    printf("executando...\n");
    FILE *f = fopen("input.txt", "r");
    struct AutomatoList *automatos = NULL;
    if (f != NULL)
    {
        automatos = readInput(f);
        startNuxmv(automatos);
        delAutomatoList(automatos);
        // fclose(f);
    }
    // struct State *state1 = newState("teste1");
    // struct State *state2 = newState("teste2");
    // struct State *state3 = newState("teste3");
    // struct Automato *automatoTeste = newAutomato("automato");

    // struct Condition condition = {"portA", '=', "50"};
    // struct Condition conditionB = {"portB", '=', "30"};
    // struct Condition *conditions = malloc(1 * sizeof(struct Condition));
    // conditions[0] = condition;
    // struct Condition *conditions2 = malloc(2 * sizeof(struct Condition));
    // conditions2[0] = condition;
    // conditions2[1] = conditionB;
    // struct Transition transition1 = {state1, state3, 1, conditions};
    // addTransition(&transition1);
    // addTransition(&transition1);
    // addTransition(&transition1);
    // struct Transition transition2 = {state2, state3, 2, conditions2};
    // struct Transition transition3 = {state3, state2, 1, conditions};
    // addTransition(&transition2);
    // addTransition(&transition3);

    // addState(state1, automatoTeste);
    // addState(state2, automatoTeste);
    // addState(state3, automatoTeste);
    // int nAutomatos = 2;
    // struct Automato *automatos[nAutomatos];
    // automatos[0] = automatoTeste;
    // automatos[1] = automatoTeste;

    // free(conditions);
    // delAutomato(automatoTeste);
    // delState(state1);
    // delState(state2);
    // delState(state3);
}
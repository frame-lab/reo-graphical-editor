#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include "state.h"

struct State *newState(char name[600], int init)
{
    struct State *state = (struct State *)malloc(sizeof(struct State));
    if (state == NULL)
        return NULL;
    strcpy(state->name, name);
    state->nTrans = 0;
    state->transitions = NULL;
    state->init = init;
    return state;
}

void addTransition(struct Transition *transition)
{
    struct State *stateStart = transition->start;
    stateStart->nTrans++;
    if (stateStart->transitions == NULL)
    {
        stateStart->transitions = (struct TransitionList *)malloc(sizeof(struct TransitionList));
        stateStart->transitions->transition = transition;
        stateStart->transitions->nextTransition = NULL;
        return;
    }
    struct TransitionList *tempTransition = stateStart->transitions;
    while (tempTransition->nextTransition != NULL)
        tempTransition = tempTransition->nextTransition;
    tempTransition->nextTransition = (struct TransitionList *)malloc(sizeof(struct TransitionList));
    tempTransition->nextTransition->transition = transition;
    tempTransition->nextTransition->nextTransition = NULL;
}

void delConditionList(struct ConditionList *conditions)
{
    if (!conditions)
        return;
    delConditionList(conditions->nextCondition);
    free(conditions->condition);
    free(conditions);
}

void delTransition(struct Transition *transition)
{
    delStringList(transition->ports);
    if (transition)
    {
        free(transition->condition);
        free(transition);
    }
}

void delTransitionList(struct TransitionList *transitions)
{
    if (transitions == NULL)
        return;
    delTransitionList(transitions->nextTransition);
    delTransition(transitions->transition);
    free(transitions);
}

void delState(struct State *state)
{
    if (state != NULL)
    {
        if (state->transitions != NULL)
            delTransitionList(state->transitions);
        free(state);
    }
}

struct State *findState(struct StateList *states, char name[600])
{
    while (states != NULL)
    {
        if (strcmp(states->state->name, name) == 0)
            return states->state;
        states = states->nextState;
    }
    return NULL;
}

struct Automato *newAutomato(char name[600])
{
    struct Automato *automato = (struct Automato *)malloc(sizeof(struct Automato));
    if (automato == NULL)
        return NULL;
    strcpy(automato->name, name);
    automato->nStates = 0;
    automato->states = NULL;
    return automato;
}

struct AutomatoProd *newAutomatoProd()
{
    struct AutomatoProd *automato = (struct AutomatoProd *)malloc(sizeof(struct AutomatoProd));
    if (automato == NULL)
        return NULL;
    automato->automato = NULL;
    automato->prod1 = NULL;
    automato->prod2 = NULL;
    automato->invar = NULL;
    automato->inalcStates = NULL;
    return automato;
}

int existString(struct StringList *list, char *string)
{
    while (list != NULL)
    {
        if (strcmp(list->string, string) == 0)
            return 1;
        list = list->nextString;
    }
    return 0;
}

void addPorts(struct TransitionList *transitions, struct Automato *automato)
{
    struct StringList *temp;
    while (transitions != NULL)
    {
        temp = transitions->transition->ports;
        while (temp != NULL)
        {
            if (!existString(automato->ports, temp->string))
            {
                automato->nPorts++;
                automato->ports = addString(automato->ports, temp->string);
            }
            temp = temp->nextString;
        }
        transitions = transitions->nextTransition;
    }
}

void addStateWithoutPorts(struct State *state, struct Automato *automato)
{
    automato->states = addStateToList(automato->states, state);
    automato->nStates++;
}

void addState(struct State *state, struct Automato *automato)
{
    addPorts(state->transitions, automato);
    automato->states = addStateToList(automato->states, state);
    automato->nStates++;
}

struct StateList *addStateToList(struct StateList *states, struct State *state)
{
    struct StateList *tempStates = states;
    struct StateList *temp = (struct StateList *)malloc(sizeof(struct StateList));
    temp->state = state;
    temp->nextState = NULL;
    if (states == NULL)
    {
        return temp;
    }
    while (tempStates->nextState != NULL)
    {
        tempStates = tempStates->nextState;
    }
    tempStates->nextState = temp;
    return states;
}

void delStatesList(struct StateList *states)
{
    if (states == NULL)
        return;
    delStatesList(states->nextState);
    delState(states->state);
    free(states);
}

void delAutomato(struct Automato *automato)
{
    if (automato != NULL)
    {
        if (automato->states)
        {
            delStatesList(automato->states);
        }
        free(automato->ports);
        free(automato);
    }
}

void delAutomatoProd(struct AutomatoProd *automato)
{
    if (automato != NULL)
    {
        free(automato->prod1);
        free(automato->prod2);
        delStringList(automato->invar);
        delStringList(automato->inalcStates);
        free(automato);
    }
}

struct StringList *addString(struct StringList *stringlist, char *string)
{
    if (stringlist == NULL)
    {
        stringlist = (struct StringList *)malloc(sizeof(struct StringList));
        stringlist->string = (char *)malloc((strlen(string) + 1) * sizeof(char));
        strcpy(stringlist->string, string);
        stringlist->nextString = NULL;
        return stringlist;
    }
    struct StringList *tempString = stringlist;
    while (tempString->nextString != NULL)
        tempString = tempString->nextString;
    tempString->nextString = (struct StringList *)malloc(sizeof(struct StringList));
    tempString->nextString->string = (char *)malloc((strlen(string) + 1) * sizeof(char));
    strcpy(tempString->nextString->string, string);
    tempString->nextString->nextString = NULL;
    return stringlist;
}

void delStringList(struct StringList *stringList)
{
    if (stringList == NULL)
        return;
    delStringList(stringList->nextString);
    if (stringList->string != NULL)
        free(stringList->string);
    free(stringList);
}

struct StringList *delString(struct StringList *stringList, char *string)
{
    if (stringList == NULL || string == NULL)
    {
        return stringList;
    }
    struct StringList *temp = stringList;
    struct StringList *first = stringList;
    if (strcmp(stringList->string, string) == 0)
    {
        temp = stringList->nextString;
        free(stringList);
        return temp;
    }
    stringList = stringList->nextString;
    while (stringList != NULL)
    {
        if (strcmp(stringList->string, string) == 0)
        {
            temp->nextString = stringList->nextString;
            free(stringList);
            return first;
        }
        temp = stringList;
        stringList = stringList->nextString;
    }
    return first;
}

struct StringList *cpyStringList(struct StringList *newList, struct StringList *stringList)
{
    if (stringList == NULL)
        return NULL;
    newList = (struct StringList *)malloc(sizeof(struct StringList));
    newList->string = (char *)malloc((strlen(stringList->string) + 1) * sizeof(char));
    strcpy(newList->string, stringList->string);
    newList->nextString = cpyStringList(newList->nextString, stringList->nextString);
    return newList;
}

struct AutomatoList *addAutomato(struct AutomatoList *automatoList, struct Automato *automato)
{
    if (automatoList == NULL)
    {
        automatoList = (struct AutomatoList *)malloc(sizeof(struct AutomatoList));
        automatoList->automato = automato;
        automatoList->nextAutomato = NULL;
        return automatoList;
    }
    struct AutomatoList *tempAutomato = automatoList;
    while (tempAutomato->nextAutomato != NULL)
        tempAutomato = tempAutomato->nextAutomato;
    tempAutomato->nextAutomato = (struct AutomatoList *)malloc(sizeof(struct AutomatoList));
    tempAutomato->nextAutomato->automato = automato;
    tempAutomato->nextAutomato->nextAutomato = NULL;
    return automatoList;
}

struct AutomatoProdList *addAutomatoProd(struct AutomatoProdList *automatoList, struct AutomatoProd *automato)
{
    if (automatoList == NULL)
    {
        automatoList = (struct AutomatoProdList *)malloc(sizeof(struct AutomatoProdList));
        automatoList->automato = automato;
        automatoList->nextAutomato = NULL;
        return automatoList;
    }
    struct AutomatoProdList *tempAutomato = automatoList;
    while (tempAutomato->nextAutomato != NULL)
        tempAutomato = tempAutomato->nextAutomato;
    tempAutomato->nextAutomato = (struct AutomatoProdList *)malloc(sizeof(struct AutomatoProdList));
    tempAutomato->nextAutomato->automato = automato;
    tempAutomato->nextAutomato->nextAutomato = NULL;
    return automatoList;
}

struct ConditionList *addConditionToList(struct ConditionList *conditionList, struct Condition *condition)
{
    if (conditionList == NULL)
    {
        conditionList = (struct ConditionList *)malloc(sizeof(struct ConditionList));
        conditionList->condition = condition;
        conditionList->nextCondition = NULL;
        return conditionList;
    }
    struct ConditionList *tempCondition = conditionList;
    while (tempCondition->nextCondition != NULL)
        tempCondition = tempCondition->nextCondition;
    tempCondition->nextCondition = (struct ConditionList *)malloc(sizeof(struct ConditionList));
    tempCondition->nextCondition->condition = condition;
    tempCondition->nextCondition->nextCondition = NULL;
    return conditionList;
}

void delAutomatoList(struct AutomatoList *automatos)
{
    if (!automatos)
        return;
    delAutomatoList(automatos->nextAutomato);
    delAutomato(automatos->automato);
    free(automatos);
}

void delAutomatoProdList(struct AutomatoProdList *automatos)
{
    if (!automatos)
        return;
    delAutomatoProdList(automatos->nextAutomato);
    delAutomatoProd(automatos->automato);
    free(automatos);
}

struct StringList *concatStringList(struct StringList *firstList, struct StringList *secondList)
{
    if (firstList == NULL)
    {
        if (secondList == NULL)
            return NULL;
        return secondList;
    }
    if (secondList == NULL)
        return firstList;
    struct StringList *temp = firstList;
    while (firstList != NULL)
    {
        if (firstList->nextString == NULL)
        {
            firstList->nextString = secondList;
            return temp;
        }
    }
}

struct StringList *unionStringList(struct StringList *firstList, struct StringList *secondList)
{
    if (firstList == NULL)
    {
        if (secondList == NULL)
            return NULL;
        return cpyStringList(NULL, secondList);
    }
    if (secondList == NULL)
        return cpyStringList(NULL, firstList);
    struct StringList *unionStringList = NULL;
    while (firstList != NULL)
    {
        if (!existString(unionStringList, firstList->string))
            unionStringList = addString(unionStringList, firstList->string);
        firstList = firstList->nextString;
    }
    while (secondList != NULL)
    {
        if (!existString(unionStringList, secondList->string))
            unionStringList = addString(unionStringList, secondList->string);
        secondList = secondList->nextString;
    }
    return unionStringList;
}

int listLength(struct StringList *list)
{
    int length = 0;
    while (list != NULL)
    {
        length++;
        list = list->nextString;
    }
    return length;
}

void printsList(struct StringList *list)
{
    if (list == NULL)
    {
        printf("Empty list\n");
    }
    else
    {
        printf("----------List---------\n");
    }
    while (list != NULL)
    {
        printf("%s\n", list->string);
        list = list->nextString;
    }
}

void printTransition(struct Transition *transition)
{
    printf("%s->%s %d\n", transition->start->name, transition->end->name, transition->nPorts);
    printsList(transition->ports);
    printf("%s\n------------------------------------\n", transition->condition);
}

void printTransitions(struct TransitionList *transisitions)
{
    while (transisitions != NULL)
    {
        printTransition(transisitions->transition);
        transisitions = transisitions->nextTransition;
    }
}

void printState(struct State *state)
{
    printf("%s--%d\n", state->name, state->nTrans);
    printTransitions(state->transitions);
}

void printAutomato(struct Automato *automato)
{
    printf("-----Automato: %s-----\n", automato->name);
    printf("Ports: %d\n", automato->nPorts);
    printsList(automato->ports);
    printf("-----States: %d-----\n", automato->nStates);
    struct StateList *states = automato->states;
    printStateList(automato->states);
}

void printStateList(struct StateList *states)
{
    while (states != NULL)
    {
        printState(states->state);
        printf("----------------------\n");
        states = states->nextState;
    }
}

struct TransitionList *addTransitions(struct TransitionList *transitions, struct TransitionList *newTransitions)
{
    struct TransitionList *trans = NULL;
    struct TransitionList *resp = transitions;
    while (newTransitions != NULL)
    {
        trans = (struct TransitionList *)malloc(sizeof(struct TransitionList));
        trans->transition = newTransitions->transition;
        trans->nextTransition = resp;
        resp = trans;
        newTransitions = newTransitions->nextTransition;
    }
    if (trans == NULL)
    {
        return resp;
    }
    return trans;
}

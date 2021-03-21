#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "state.h"

void nullPorts(struct StringList *ports, struct Transition *transition, FILE *f)
{
    int exists = 0;
    struct StringList *portsTrans = transition->ports;
    while (ports != NULL)
    {
        if (!existString(portsTrans, ports->string))
        {
            fprintf(f, "ports.%s[time] = NULL & ", ports->string);
        }
        ports = ports->nextString;
    }
}

void caToNuxmv(struct Automato *automato, struct StringList *ports, FILE *f)
{
    int nStates = automato->nStates;
    struct StateList *states = automato->states;
    int first = 0;
    struct StringList *statesNames = NULL;
    struct StringList *tempStatesNames = NULL;
    if (automato->lineCount != 0)
    {
        fprintf(f, "--Channel from line %d on the input file\n", automato->lineCount);
    }
    fprintf(f, "MODULE %s(time)\nVAR\n\tports: ", automato->name);
    fprintf(f, "portsModule;\n");
    fprintf(f, "\tcs: {");
    struct TransitionList *allTransitions = NULL;
    while (states != NULL)
    {
        fprintf(f, "%s%s", states->state->name, states->nextState != NULL ? "," : "");
        statesNames = addString(statesNames, states->state->name);
        allTransitions = addTransitions(allTransitions, states->state->transitions);
        states = states->nextState;
    }
    fprintf(f, "};\n");
    states = automato->states;
    if (states->nextState != NULL)
    {
        fprintf(f, "ASSIGN\n\tinit(cs) := {");
        while (states != NULL)
        {
            if (states->state->init)
            {
                fprintf(f, "%s%s", first ? "," : "", states->state->name);
                first++;
            }
            states = states->nextState;
        }
        fprintf(f, "};\n");
        states = automato->states;
    }
    struct TransitionList *transitions = NULL;
    struct ConditionList *conditions;
    int second = 0;
    char operation[2];
    operation[1] = '\0';
    int printTrans = 1;
    int closeTransition = 0;
    while (states != NULL)
    {
        transitions = allTransitions;
        delStringList(tempStatesNames);
        tempStatesNames = cpyStringList(tempStatesNames, statesNames);
        tempStatesNames = delString(tempStatesNames, states->state->name);
        second = 0;
        closeTransition = 0;
        while (transitions != NULL)
        {
            if (transitions->transition->start->name == states->state->name)
                tempStatesNames = delString(tempStatesNames, transitions->transition->end->name);
            if (printTrans && transitions->transition->blocked != 1)
            {
                fprintf(f, "TRANS\n\t");
                printTrans = 0;
            }
            if (transitions->transition->end->name == states->state->name && transitions->transition->blocked != 1)
            {
                fprintf(f, "%s(cs = %s & ", second ? "\n\t| " : "(", transitions->transition->start->name);
                nullPorts(ports, transitions->transition, f);
                fprintf(f, " %s%s)", transitions->transition->condition, transitions->transition->blocked == 1 ? " & FALSE" : "");
                second++;
                closeTransition = 1;
            }
            transitions = transitions->nextTransition;
        }
        if (second)
        {
            fprintf(f, " <-> next(cs) = %s)", states->state->name);
        }
        if (tempStatesNames)
        {
            if (printTrans)
            {
                fprintf(f, "TRANS\n\t");
                printTrans = 0;
            }
            fprintf(f, "%s((cs = %s) -> (", second ? " &\n\t" : "", states->state->name);
            while (tempStatesNames != NULL)
            {
                fprintf(f, "(next(cs) != %s)%s", tempStatesNames->string, tempStatesNames->nextString != NULL ? " & " : "))");
                tempStatesNames = tempStatesNames->nextString;
                closeTransition = 1;
            }
        }
        if (closeTransition == 1)
        {
            fprintf(f, "%s", states->nextState != NULL ? " &\n\t" : ";\n\n");
        }
        states = states->nextState;
    }
    if (printTrans)
        fprintf(f, "\n");
}

struct StringList *portsIntersection(struct Transition *transition, struct Automato *automato)
{
    struct StringList *list = NULL;
    char *concat = (char *)malloc(800 * sizeof(char));
    struct StringList *ports = transition->ports;
    struct StringList *portsAutomato = automato->ports;
    while (ports != NULL)
    {
        portsAutomato = automato->ports;
        while (portsAutomato != NULL)
        {
            if (strcmp(ports->string, portsAutomato->string) == 0)
            {
                strcpy(concat, portsAutomato->string);
                list = addString(list, concat);
            }
            portsAutomato = portsAutomato->nextString;
        }
        ports = ports->nextString;
    }
    return list;
}

int equalIntersections(struct StringList *list1, struct StringList *list2)
{
    if (list1 == NULL && list2 != NULL)
    {
        return 0;
    }
    int equal = 1;
    int matches = 0;
    struct StringList *list1Start = list1;
    struct StringList *list2Start = list2;
    int list1Len = 0;
    int list2Len = 0;
    int firtsPass = 1;
    while (list1 != NULL)
    {
        list2 = list2Start;
        while (list2 != NULL)
        {
            if (list1Len == 0)
            {
                list2Len++;
            }
            if (strcmp(list1->string, list2->string) == 0)
            {
                matches = 1;
                if (list1Len != 0)
                {
                    break;
                }
            }
            list2 = list2->nextString;
        }
        list1Len++;
        if (!matches)
            return 0;
        matches = 0;
        list1 = list1->nextString;
    }
    if (list2Len > list1Len)
    {
        list1 = list1Start;
        list2 = list2Start;
        while (list2 != NULL)
        {
            list1 = list1Start;
            while (list1 != NULL)
            {
                if (strcmp(list2->string, list1->string) == 0)
                {
                    matches = 1;
                    break;
                }
                list1 = list1->nextString;
            }
            if (!matches)
                return 0;
            matches = 0;
            list2 = list2->nextString;
        }
    }
    return 1;
}

int equalPorts(struct Transition *transition1, struct Transition *transition2)
{
    int equal = 0;
    struct StringList *biggerConditions;
    struct StringList *lesserConditions;
    struct StringList *tempLesserConditions;
    if (transition1->nPorts > transition2->nPorts)
    {
        biggerConditions = transition1->ports;
        lesserConditions = transition2->ports;
    }
    else
    {
        biggerConditions = transition2->ports;
        lesserConditions = transition1->ports;
    }
    tempLesserConditions = lesserConditions;
    while (biggerConditions != NULL)
    {
        lesserConditions = tempLesserConditions;
        while (lesserConditions != NULL)
        {
            if (strcmp(biggerConditions->string, lesserConditions->string) == 0)
            {
                equal = 1;
                break;
            }
            lesserConditions = lesserConditions->nextString;
        }
        if (!equal)
            return 0;
        equal = 0;
        biggerConditions = biggerConditions->nextString;
    }
    return 1;
}

void printToNuXmv(struct StringList *trans, struct StringList *states, struct StringList *invar,
                  struct StringList *components, struct StringList *initStates, char *automatoName, FILE *f)
{
    int initState = states->nextString != NULL ? 1 : 0;
    fprintf(f, "MODULE %s(time)\nVAR\n", automatoName);
    fprintf(f, "\tprod1: %s(time);\n\tprod2: %s(time);\n\tports: portsModule;\n",
            components->string, components->nextString->string);
    fprintf(f, "\tcs: {");
    while (states != NULL)
    {
        fprintf(f, "%s%s", states->string, states->nextString != NULL ? "," : "");
        states = states->nextString;
    }
    fprintf(f, "};\n");
    if (initState)
    {
        fprintf(f, "ASSIGN\n\tinit(cs) := {");
        while (initStates != NULL)
        {
            fprintf(f, "%s%s", initStates->string, initStates->nextString != NULL ? "," : "};\n");
            initStates = initStates->nextString;
        }
    }
    if (trans != NULL)
    {
        fprintf(f, "TRANS\n");
        while (trans != NULL)
        {
            fprintf(f, "\t%s%s", trans->string, trans->nextString != NULL ? ") &\n" : ");\n");
            trans = trans->nextString;
        }
    }
    fprintf(f, "INVAR\n");
    while (invar != NULL)
    {
        fprintf(f, "\t%s%s", invar->string, invar->nextString != NULL ? " &\n" : ";\n\n");
        invar = invar->nextString;
    }
}
void randomPort(FILE *f, char *port, int timeMax)
{
    int valueCase;
    for (size_t i = 0; i < timeMax; i++)
    {
        valueCase = random() % 3;
        if (valueCase == 0)
            fprintf(f, "\tinit(%s[%ld]) := 0;\n", port, i);
        else if (valueCase == 1)
            fprintf(f, "\tinit(%s[%ld]) := 1;\n", port, i);
        else
            fprintf(f, "\tinit(%s[%ld]) := NULL;\n", port, i);
    }
}

int portsToNuXmv(FILE *f, struct StringList *ports)
{
    FILE *pFile = fopen("ports.txt", "r");
    int timeMax = 0;
    struct StringList *portValues = NULL;
    struct StringList *portsFile = NULL;
    if (pFile != NULL)
    {
        int i, j, length;
        char line[128];
        char value[128];
        char port[128];
        char *temp = (char *)malloc(600 * sizeof(char));
        fgets(line, sizeof line, pFile);
        if (strcmp(line, "list\n") == 0)
        {
            while (fgets(line, sizeof line, pFile) != NULL)
            {
                i = 0;
                while (line[i] != ',')
                {
                    port[i] = line[i];
                    i++;
                }
                port[i] = '\0';
                portsFile = addString(portsFile, port);
                length = 0;
                while ((line[i] != '\n') && (line[i] != '\0'))
                {
                    i++;
                    j = 0;
                    while (line[i] != ',' && line[i] != '\n' && line[i] != '\0')
                    {
                        value[j] = line[i];
                        i++;
                        j++;
                    }
                    value[j] = '\0';
                    snprintf(temp, 6000, "\tinit(%s[%d]) := %s;\n", port, length, value);
                    portValues = addString(portValues, temp);
                    length++;
                }
                if (length > timeMax)
                    timeMax = length;
            }
        }
    }
    struct StringList *tempPorts = ports;
    int valueCase;
    if (timeMax == 0)
        timeMax = 5;
    fprintf(f, "MODULE portsModule\nFROZENVAR\n");
    while (tempPorts != NULL)
    {
        fprintf(f, "\t%s : array 0..%d of {NULL, 0, 1};\n", tempPorts->string, timeMax - 1);
        tempPorts = tempPorts->nextString;
    }
    fprintf(f, "ASSIGN\n");
    while (portValues != NULL)
    {
        fprintf(f, "%s", portValues->string);
        portValues = portValues->nextString;
    }
    tempPorts = cpyStringList(tempPorts, ports);
    while (portsFile != NULL)
    {
        tempPorts = delString(tempPorts, portsFile->string);
        portsFile = portsFile->nextString;
    }
    while (tempPorts != NULL)
    {
        randomPort(f, tempPorts->string, timeMax);
        tempPorts = tempPorts->nextString;
    }
    fprintf(f, "\n");
    delStringList(tempPorts);
    tempPorts = NULL;
    return timeMax;
}

void printaAutomatoFinal(struct Automato *automato)
{
    FILE *f = fopen("nuxmv2.smv", "w");
    if (f == NULL)
    {
        printf("Error opening file!\n");
        exit(1);
    }
    int time = portsToNuXmv(f, automato->ports) - 1;
    fprintf(f, "MODULE main\nVAR\n\ttime: 0..%d;\n\tautomato: %s(time);\n", time, automato->name);
    fprintf(f, "ASSIGN\n\tinit(time) := 0;\n\tnext(time) := case\n\t\ttime < %d: time + 1;\n\t\tTRUE: time;\nesac;\n\n", time);
    fprintf(f, "--Final product, corresponding to the full circuit\n");
    caToNuxmv(automato, automato->ports, f);

    fclose(f);
}

char *nullPortsToString(struct StringList *portsAutomato, struct StringList *ports)
{
    char *nullPortsString = (char *)malloc(600 * sizeof(char));
    char *nullPort = (char *)malloc(600 * sizeof(char));
    while (portsAutomato != NULL)
    {
        if (!existString(ports, portsAutomato->string))
        {
            snprintf(nullPort, 6000, " & ports.%s[time] = NULL", portsAutomato->string);
            strcat(nullPortsString, nullPort);
        }
        portsAutomato = portsAutomato->nextString;
    }
    return nullPortsString;
}

struct AutomatoProdList *productInSmv(struct AutomatoList *automatos, struct StringList *ports, FILE *f)
{
    struct Automato *automato1 = automatos->automato;
    struct Automato *automato2;
    char *concat = (char *)malloc(8000 * sizeof(char));
    char *tempCondition = NULL;
    char *tempAdd = NULL;
    char *transString = (char *)malloc(12000 * sizeof(char));
    struct StringList *intersection1 = NULL;
    struct StringList *intersection2 = NULL;
    struct StateList *states1;
    struct StateList *states2;
    struct TransitionList *transitions1 = NULL;
    struct TransitionList *transitions2 = NULL;
    struct StringList *trans = NULL;
    struct StringList *invar = NULL;
    struct StringList *states = NULL;
    struct StringList *initStates = NULL;
    struct StringList *components = NULL;
    struct StringList *inalcStates = NULL;
    struct StringList *automatoPorts = NULL;
    struct ConditionList *conditions;
    struct State *tempState = NULL;
    struct State *stateStart = NULL;
    struct StateList *tempStates = NULL;
    struct Transition *tempTransition = NULL;
    struct StringList *tempPorts = NULL;
    int init;
    int tempNPorts;
    int firstPass = 1;
    struct AutomatoProd *prod;
    struct AutomatoProdList *prods = NULL;

    while (automatos->nextAutomato != NULL)
    {
        automato2 = automatos->nextAutomato->automato;
        states1 = automato1->states;
        components = NULL;
        components = addString(components, automato1->name);
        components = addString(components, automato2->name);
        automatoPorts = unionStringList(automato1->ports, automato2->ports);
        delStringList(states);
        delStringList(initStates);
        // delStringList(invar);
        // delStringList(trans);
        states = NULL;
        initStates = NULL;
        invar = NULL;
        trans = NULL;
        while (states1 != NULL)
        {
            states2 = automato2->states;
            while (states2 != NULL)
            {
                init = ((states1->state->init + states2->state->init) == 2 ? 1 : 0);
                snprintf(concat, 8000, "%s%s", states1->state->name, states2->state->name);
                states = addString(states, concat);
                if (init)
                    initStates = addString(initStates, concat);
                snprintf(transString, 20000, "(((prod1.cs = %s) & (prod2.cs = %s)) <-> (cs = %s))", states1->state->name, states2->state->name, concat);
                invar = addString(invar, transString);
                states2 = states2->nextState;
                tempState = newState(concat, init);
                tempStates = addStateToList(tempStates, tempState);
            }
            states1 = states1->nextState;
        }
        states1 = automato1->states;
        states2 = automato2->states;
        while (states1 != NULL)
        {
            states2 = automato2->states;
            while (states2 != NULL)
            {
                snprintf(concat, 8000, "%s%s", states1->state->name, states2->state->name);
                stateStart = findState(tempStates, concat);
                transitions1 = states1->state->transitions;
                // delStringList(inalcStates);
                inalcStates = NULL;
                inalcStates = cpyStringList(inalcStates, states);
                snprintf(concat, 8000, "%s%s", states1->state->name, states2->state->name);
                inalcStates = delString(inalcStates, concat);
                firstPass = 1;
                while (transitions1 != NULL)
                {
                    intersection1 = portsIntersection(transitions1->transition, automato2);
                    if (intersection1 == NULL)
                    {
                        snprintf(concat, 8000, "%s%s", transitions1->transition->end->name, states2->state->name);
                        inalcStates = delString(inalcStates, concat);
                        tempState = findState(tempStates, concat);
                        tempTransition = (struct Transition *)malloc(sizeof(struct Transition));
                        tempTransition->start = stateStart;
                        tempTransition->end = tempState;
                        tempTransition->nPorts = transitions1->transition->nPorts;
                        tempTransition->ports = transitions1->transition->ports;
                        tempTransition->condition = transitions1->transition->condition;
                        tempTransition->add = transitions1->transition->add;
                        tempTransition->blocked = 2;
                        addTransition(tempTransition);
                    }
                    else
                    {
                        transitions1->transition->blocked = 1;
                    }
                    transitions2 = states2->state->transitions;
                    while (transitions2 != NULL)
                    {
                        intersection2 = portsIntersection(transitions2->transition, automato1);
                        if (firstPass && states1->nextState == NULL)
                            if (intersection2 == NULL)
                            {
                                snprintf(concat, 6000, "%s%s", states1->state->name, transitions2->transition->end->name);
                                inalcStates = delString(inalcStates, concat);
                                tempState = findState(tempStates, concat);
                                tempTransition = (struct Transition *)malloc(sizeof(struct Transition));
                                tempTransition->start = stateStart;
                                tempTransition->end = tempState;
                                tempTransition->nPorts = transitions2->transition->nPorts;
                                tempTransition->ports = transitions2->transition->ports;
                                tempTransition->condition = transitions2->transition->condition;
                                tempTransition->add = transitions2->transition->add;
                                tempTransition->blocked = 2;
                                addTransition(tempTransition);
                            }
                            else
                            {
                                transitions2->transition->blocked = 1;
                            }
                        if (equalIntersections(intersection1, intersection2))
                        {
                            snprintf(concat, 6000, "%s%s", transitions1->transition->end->name, transitions2->transition->end->name);
                            inalcStates = delString(inalcStates, concat);
                            // tempNPorts = transitions1->transition->nPorts;
                            // tempPorts = transitions1->transition->ports;
                            tempTransition = (struct Transition *)malloc(sizeof(struct Transition));
                            // tempTransition->blocked = 2;
                            // if (!equalPorts(transitions1->transition, transitions2->transition))
                            // {
                            tempPorts = unionStringList(transitions1->transition->ports, transitions2->transition->ports);
                            tempNPorts = listLength(tempPorts);
                            tempTransition->blocked = 0;
                            // }
                            // if (intersection1 == NULL && intersection2 == NULL)
                            // {
                            //     tempPorts = unionStringList(transitions1->transition->ports, transitions2->transition->ports);
                            //     tempNPorts = listLength(tempPorts);
                            // }
                            tempState = findState(tempStates, concat);
                            tempTransition->start = stateStart;
                            tempTransition->end = tempState;
                            tempTransition->nPorts = tempNPorts;
                            tempTransition->ports = tempPorts;
                            tempCondition = (char *)malloc(6000 * sizeof(char));
                            snprintf(tempCondition, 6000, "%s & %s", transitions1->transition->condition, transitions2->transition->condition);
                            tempTransition->condition = tempCondition;
                            tempAdd = (char *)malloc(6000 * sizeof(char));
                            snprintf(tempAdd, 6000, "%s & %s", transitions1->transition->add, transitions2->transition->add);
                            tempTransition->add = tempAdd;
                            addTransition(tempTransition);
                        }
                        transitions2 = transitions2->nextTransition;
                    }
                    firstPass = 0;
                    transitions1 = transitions1->nextTransition;
                }
                if (states1->state->transitions == NULL && states1->nextState == NULL)
                {
                    transitions2 = states2->state->transitions;
                    while (transitions2 != NULL)
                    {
                        intersection2 = portsIntersection(transitions2->transition, automato1);
                        if (intersection2 == NULL)
                        {
                            snprintf(concat, 6000, "%s%s", states1->state->name, transitions2->transition->end->name);
                            inalcStates = delString(inalcStates, concat);
                            tempState = findState(tempStates, concat);
                            tempTransition = (struct Transition *)malloc(sizeof(struct Transition));
                            tempTransition->start = stateStart;
                            tempTransition->end = tempState;
                            tempTransition->nPorts = transitions2->transition->nPorts;
                            tempTransition->ports = transitions2->transition->ports;
                            tempTransition->condition = transitions2->transition->condition;
                            tempTransition->add = transitions2->transition->add;
                            tempTransition->blocked = 2;
                            addTransition(tempTransition);
                        }
                        else
                        {
                            transitions2->transition->blocked = 1;
                        }
                        transitions2 = transitions2->nextTransition;
                    }
                }
                if (inalcStates != NULL)
                {
                    snprintf(transString, 12000, "((cs = %s%s) -> (", states1->state->name, states2->state->name);
                    while (inalcStates != NULL)
                    {
                        snprintf(concat, 8000, "(next(cs) != %s)%s", inalcStates->string, inalcStates->nextString != NULL ? " & " : "))");
                        strcat(transString, concat);
                        inalcStates = inalcStates->nextString;
                    }
                    trans = addString(trans, transString);
                }
                states2 = states2->nextState;
            }
            states1 = states1->nextState;
        }
        tempAdd = (char *)malloc(6000 * sizeof(char));
        snprintf(tempAdd, 6000, "%s & %s", automato1->add, automato2->add);
        if (automatos->nextAutomato->nextAutomato == NULL)
            strcpy(concat, "finalAutomata\0");
        else
            snprintf(concat, 6000, "%s%s", components->string, components->nextString->string);
        automato1 = newAutomato(concat, 0);
        automato1->ports = automatoPorts;
        automato1->nPorts = listLength(automatoPorts);
        automato1->add = tempAdd;
        while (tempStates != NULL)
        {
            addStateWithoutPorts(tempStates->state, automato1);
            tempStates = tempStates->nextState;
        }
        prod = newAutomatoProd();
        prod->automato = automato1;
        prod->prod1 = components->string;
        prod->prod2 = components->nextString->string;
        prod->invar = invar;
        prod->inalcStates = trans;
        prods = addAutomatoProd(prods, prod);
        automatos = automatos->nextAutomato;
        tempStates = NULL;
    }
    return prods;
}
void prodToNuxmv(struct AutomatoProd *prod, struct StringList *ports, FILE *f, int finalAutomata)
{
    struct Automato *automato = prod->automato;
    struct StateList *states = automato->states;
    struct StringList *inalcStates = prod->inalcStates;
    struct StringList *invar = prod->invar;
    struct TransitionList *allTransitions = NULL;
    int first = 0;
    if (finalAutomata != 1)
    {
        fprintf(f, "--Product between %s and %s\n", prod->prod1, prod->prod2);
    }
    else
    {
        fprintf(f, "--Final product, corresponding to the full circuit\n");
    }
    fprintf(f, "MODULE %s(time)\nVAR\n\tprod1: %s(time);\n\tprod2: %s(time);\n\tports: ", automato->name, prod->prod1, prod->prod2);
    fprintf(f, "portsModule;\n");
    fprintf(f, "\tcs: {");
    while (states != NULL)
    {
        fprintf(f, "%s%s", states->state->name, states->nextState != NULL ? "," : "");
        allTransitions = addTransitions(allTransitions, states->state->transitions);
        states = states->nextState;
    }
    fprintf(f, "};\n");
    states = automato->states;
    if (states->nextState != NULL)
    {
        fprintf(f, "ASSIGN\n\tinit(cs) := {");
        while (states != NULL)
        {
            if (states->state->init)
            {
                fprintf(f, "%s%s", first ? "," : "", states->state->name);
                first++;
            }
            states = states->nextState;
        }
        fprintf(f, "};\n");
        states = automato->states;
    }
    struct TransitionList *transitions;
    int printTrans = 1;
    int second = 0;
    while (states != NULL)
    {
        transitions = allTransitions;
        second = 0;
        while (transitions != NULL)
        {
            if (printTrans)
            {
                fprintf(f, "TRANS\n\t");
                printTrans = 0;
            }
            if (transitions->transition->end->name == states->state->name && transitions->transition->blocked == 0)
            {
                fprintf(f, "%s(cs = %s & ", second ? "\n\t| " : "(", transitions->transition->start->name);
                nullPorts(ports, transitions->transition, f);
                fprintf(f, " %s%s)", transitions->transition->condition, transitions->transition->blocked == 1 ? " & FALSE" : "");
                second++;
            }
            transitions = transitions->nextTransition;
        }
        if (second)
        {
            fprintf(f, " <-> next(cs) = %s)%s", states->state->name, states->nextState ? " &\n\t" : inalcStates ? " &\n\t"
                                                                                                                : ";\n");
        }
        states = states->nextState;
    }
    while (inalcStates != NULL)
    {
        fprintf(f, "%s%s", inalcStates->string, inalcStates->nextString != NULL ? " &\n\t" : ";\n");
        inalcStates = inalcStates->nextString;
    }
    if (invar != NULL)
        fprintf(f, "INVAR\n\t");
    while (invar != NULL)
    {
        fprintf(f, "%s%s", invar->string, invar->nextString != NULL ? " &\n\t" : ";\n\n");
        invar = invar->nextString;
    }
    if (printTrans)
        fprintf(f, "\n");
}

void startNuxmv(struct AutomatoList *automatos)
{
    struct AutomatoList *automatoList = automatos;
    struct AutomatoProdList *prods, *prodsTemp;
    struct StringList *ports;
    FILE *f = fopen("nuxmv.smv", "w");
    if (f == NULL)
    {
        printf("Error opening file!\n");
        exit(1);
    }
    while (automatoList != NULL)
    {
        ports = unionStringList(ports, automatoList->automato->ports);
        automatoList = automatoList->nextAutomato;
    }
    int time = portsToNuXmv(f, ports) - 1;
    prods = productInSmv(automatos, ports, f);
    prodsTemp = prods;
    automatoList = automatos;
    fprintf(f, "MODULE main\nVAR\n\ttime: 0..%d;\n\t%s: %s(time);\n", time, "finalAutomata", "finalAutomata");
    fprintf(f, "ASSIGN\n\tinit(time) := 0;\n\tnext(time) := case\n\t\ttime < %d: time + 1;\n\t\tTRUE: time;\nesac;\n\n", time);
    while (automatoList != NULL)
    {
        caToNuxmv(automatoList->automato, ports, f);
        automatoList = automatoList->nextAutomato;
    }
    if (prodsTemp == NULL)
        printaAutomatoFinal(automatos->automato);
    while (prodsTemp != NULL)
    {
        if (prodsTemp->nextAutomato == NULL)
        {
            prodToNuxmv(prodsTemp->automato, ports, f, 1);
            printaAutomatoFinal(prodsTemp->automato->automato);
        }
        else
        {
            prodToNuxmv(prodsTemp->automato, ports, f, 0);
        }
        prodsTemp = prodsTemp->nextAutomato;
    }
    delStringList(ports);
    delAutomatoProdList(prods);
    fclose(f);
}

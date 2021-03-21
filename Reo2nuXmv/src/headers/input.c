#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "state.h"

struct Automato *createSync(char *ports, int nAuto, int lineCount)
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
    while (ports[i] != ')' && ports[i] != '\0')
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
    snprintf(condition, 600, "ports.%s[time] != NULL & ports.%s[time] = ports.%s[time]", port1, port1, port2);
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
    struct Automato *automato = newAutomato(automatoName, lineCount);
    addState(state1, automato);
    return automato;
}

struct Automato *createLossy(char *ports, int nAuto, int lineCount)
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
    while (ports[i] != ')' && ports[i] != '\0')
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
    snprintf(condition, 600, "ports.%s[time] != NULL & ports.%s[time] = ports.%s[time]", port1, port1, port2);
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
    snprintf(condition, 600, "ports.%s[time] != NULL", port1);
    transition = (struct Transition *)malloc(sizeof(struct Transition));
    transition->start = state1;
    transition->end = state1;
    transition->ports = portsList;
    transition->condition = condition;
    transition->blocked = 0;
    addTransition(transition);
    char *automatoName = (char *)malloc(600 * sizeof(char));
    snprintf(automatoName, 600, "lossySync%d", nAuto);
    struct Automato *automato = newAutomato(automatoName, lineCount);
    addState(state1, automato);
    return automato;
}

struct Automato *createFifo(char *ports, int nAuto, int lineCount)
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
    while (ports[i] != ')' && ports[i] != '\0')
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
    snprintf(condition, 600, "ports.%s[time] = 0", port1);
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
    snprintf(condition, 600, "ports.%s[time] = 1", port1);
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
    snprintf(condition, 600, "ports.%s[time] = 1", port2);
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
    snprintf(condition, 600, "ports.%s[time] = 0", port2);
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
    struct Automato *automato = newAutomato(automatoName, lineCount);
    addState(state1, automato);
    addState(state2, automato);
    addState(state3, automato);
    return automato;
}

struct Automato *createSyncDrain(char *ports, int nAuto, int lineCount)
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
    while (ports[i] != ')' && ports[i] != '\0')
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
    snprintf(condition, 600, "ports.%s[time] != NULL & ports.%s[time] != NULL", port1, port2);
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
    struct Automato *automato = newAutomato(automatoName, lineCount);
    addState(state1, automato);
    return automato;
}

struct Automato *createAsync(char *ports, int nAuto, int lineCount)
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
    while (ports[i] != ')' && ports[i] != '\0')
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
    snprintf(condition, 600, "ports.%s[time] != NULL", port1);
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
    snprintf(condition, 600, "ports.%s[time] != NULL", port2);
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
    struct Automato *automato = newAutomato(automatoName, lineCount);
    addState(state1, automato);
    return automato;
}

struct Automato *createMerger(char *ports, int nAuto, int lineCount)
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
    while (ports[i] != ',')
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
    while (ports[i] != ')' && ports[i] != '\0')
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
    struct Automato *automato = newAutomato(automatoName, lineCount);
    addState(state1, automato);
    return automato;
}

struct Automato *createReplicator(char *ports, int nAuto, int lineCount)
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
    while (ports[i] != ',')
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
    while (ports[i] != ')' && ports[i] != '\0')
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
    struct Automato *automato = newAutomato(automatoName, lineCount);
    addState(state1, automato);
    return automato;
}

struct Automato *createFilter(char *ports, int nAuto, int lineCount)
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
    while (ports[i] != ')' && ports[i] != '\0')
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
    struct Automato *automato = newAutomato(automatoName, lineCount);
    addState(state1, automato);
    return automato;
}

struct Automato *createTransformer(char *ports, int nAuto, int lineCount)
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
    while (ports[i] != ')' && ports[i] != '\0')
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
    struct Automato *automato = newAutomato(automatoName, lineCount);
    addState(state1, automato);
    return automato;
}
struct Automato *createTimer(char *ports, int nAuto, int lineCount, char *param)
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
    while (ports[i] != ')' && ports[i] != '\0')
    {
        if (ports[i] != ' ')
        {
            port2[j] = ports[i];
            j++;
        }
        i++;
    }
    char varInicial[] = "5";
    struct State *state1 = newState("q0", 1);
    struct State *state2 = newState("p0", 0);
    char *condition = (char *)malloc(600 * sizeof(char));
    char *add = (char *)malloc(600 * sizeof(char));
    struct StringList *portsList = NULL;
    portsList = addString(portsList, port1);
    snprintf(condition, 600, "ports.%s[time] != NULL", port1);
    snprintf(add, 600, " & next(data) = ports.%s[time] & next(var) = %s", port1, varInicial);
    struct Transition *transition = (struct Transition *)malloc(sizeof(struct Transition));
    transition->start = state1;
    transition->end = state2;
    transition->nPorts = 1;
    transition->ports = portsList;
    transition->condition = condition;
    transition->blocked = 0;
    transition->add = add;
    addTransition(transition);
    condition = (char *)malloc(600 * sizeof(char));
    add = (char *)malloc(600 * sizeof(char));
    portsList = NULL;
    portsList = addString(portsList, port2);
    snprintf(condition, 600, "ports.%s[time] = data & var = 0", port2);
    snprintf(add, 600, " & next(data) = NULL");
    transition = (struct Transition *)malloc(sizeof(struct Transition));
    transition->start = state2;
    transition->end = state1;
    transition->nPorts = 1;
    transition->ports = portsList;
    transition->condition = condition;
    transition->blocked = 0;
    transition->add = add;
    addTransition(transition);
    char *automatoName = (char *)malloc(600 * sizeof(char));
    snprintf(automatoName, 600, "timer%d", nAuto);
    struct Automato *automato = newAutomato(automatoName, lineCount);
    addState(state1, automato);
    addState(state2, automato);
    add = (char *)malloc(1024 * sizeof(char));
    snprintf(add, 1024, "var > 0 <-> next(var) = (%s)", param);
    automato->add = add;
    return automato;
}

struct Automato *createTimedTransformer(char *ports, int nAuto, int lineCount, char *param)
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
    while (ports[i] != ')' && ports[i] != '\0')
    {
        if (ports[i] != ' ')
        {
            port2[j] = ports[i];
            j++;
        }
        i++;
    }
    char varInicial[] = "5";
    struct State *state1 = newState("q0", 1);
    struct State *state2 = newState("p0", 0);
    char *condition = (char *)malloc(600 * sizeof(char));
    char *add = (char *)malloc(600 * sizeof(char));
    struct StringList *portsList = NULL;
    portsList = addString(portsList, port1);
    snprintf(condition, 600, "ports.%s[time] != NULL", port1);
    snprintf(add, 600, " & next(var) = ports.%s[time]", port1);
    struct Transition *transition = (struct Transition *)malloc(sizeof(struct Transition));
    transition->start = state1;
    transition->end = state2;
    transition->nPorts = 1;
    transition->ports = portsList;
    transition->condition = condition;
    transition->blocked = 0;
    transition->add = add;
    addTransition(transition);
    condition = (char *)malloc(600 * sizeof(char));
    add = (char *)malloc(600 * sizeof(char));
    portsList = NULL;
    portsList = addString(portsList, port2);
    snprintf(condition, 600, "ports.%s[time] = var & var > %s", port2, varInicial);
    snprintf(add, 600, " & next(var) = 0");
    transition = (struct Transition *)malloc(sizeof(struct Transition));
    transition->start = state2;
    transition->end = state1;
    transition->nPorts = 1;
    transition->ports = portsList;
    transition->condition = condition;
    transition->blocked = 0;
    transition->add = add;
    addTransition(transition);
    char *automatoName = (char *)malloc(600 * sizeof(char));
    snprintf(automatoName, 600, "timedtransformer%d", nAuto);
    struct Automato *automato = newAutomato(automatoName, lineCount);
    addState(state1, automato);
    addState(state2, automato);
    add = (char *)malloc(1024 * sizeof(char));
    snprintf(add, 1024, "var > %s <-> next(var) = (%s)", varInicial, param);
    automato->add = add;
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
    char param[1024];
    int i = 0;
    int j = 0;
    int nAuto = 0;
    int lineCount = 1;
    memset(line, '\0', sizeof(line));
    while (fgets(line, sizeof line, f) != NULL)
    {
        i = 0;
        j = 0;
        memset(command, '\0', sizeof(command));
        memset(ports, '\0', sizeof(ports));
        memset(param, '\0', sizeof(param));
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
        while ((line[i] != ')') && (line[i] != '\n') && (line[i] != '\0') && line[i] != '/')
        {
            ports[j] = line[i];
            i++;
            j++;
        }
        j = 0;
        while ((line[i] != '[') && (line[i] != '\n') && (line[i] != '\0') && line[i] != '/')
        {
            i++;
        }
        i++;
        if (strcmp(command, "sync") == 0)
        {
            nAuto++;
            temp = createSync(ports, nAuto, lineCount);
            automatoList = addAutomato(automatoList, temp);
        }
        if (strcmp(command, "lossysync") == 0)
        {
            nAuto++;
            temp = createLossy(ports, nAuto, lineCount);
            automatoList = addAutomato(automatoList, temp);
        }
        if (strcmp(command, "fifo1") == 0)
        {
            nAuto++;
            temp = createFifo(ports, nAuto, lineCount);
            automatoList = addAutomato(automatoList, temp);
        }
        if (strcmp(command, "syncdrain") == 0)
        {
            nAuto++;
            temp = createSyncDrain(ports, nAuto, lineCount);
            automatoList = addAutomato(automatoList, temp);
        }
        if (strcmp(command, "syncspout") == 0)
        {
            nAuto++;
            temp = createAsync(ports, nAuto, lineCount);
            automatoList = addAutomato(automatoList, temp);
        }
        if (strcmp(command, "merger") == 0)
        {
            nAuto++;
            temp = createMerger(ports, nAuto, lineCount);
            automatoList = addAutomato(automatoList, temp);
        }
        if (strcmp(command, "replicator") == 0)
        {
            nAuto++;
            temp = createReplicator(ports, nAuto, lineCount);
            automatoList = addAutomato(automatoList, temp);
        }
        if (strcmp(command, "filter") == 0)
        {
            nAuto++;
            temp = createFilter(ports, nAuto, lineCount);
            automatoList = addAutomato(automatoList, temp);
        }
        if (strcmp(command, "transformer") == 0)
        {
            nAuto++;
            temp = createTransformer(ports, nAuto, lineCount);
            automatoList = addAutomato(automatoList, temp);
        }
        if (strcmp(command, "timer") == 0)
        {
            while ((line[i] != ';') && (line[i] != '\n') && (line[i] != '\0') && line[i] != '/')
            {
                param[j] = line[i];
                i++;
                j++;
            }
            nAuto++;
            temp = createTimer(ports, nAuto, lineCount, param);
            automatoList = addAutomato(automatoList, temp);
        }
        if (strcmp(command, "timedtransformer") == 0)
        {
            while ((line[i] != ';') && (line[i] != '\n') && (line[i] != '\0') && line[i] != '/')
            {
                param[j] = line[i];
                i++;
                j++;
            }
            nAuto++;
            temp = createTimedTransformer(ports, nAuto, lineCount, param);
            automatoList = addAutomato(automatoList, temp);
        }
        memset(line, '\0', sizeof(line));
        lineCount++;
    }
    return automatoList;
}

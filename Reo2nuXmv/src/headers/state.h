#ifndef STATE_HEADER_GUARD
#define STATE_HEADER_GUARD

struct Automato
{
    char name[600];
    int nStates;
    struct StateList *states;
    int nPorts;
    struct StringList *ports;
    int lineCount;
    char *add;
};

struct AutomatoProd
{
    struct Automato *automato;
    char *prod1;
    char *prod2;
    struct StringList *invar;
    struct StringList *inalcStates;
};

struct State
{
    char name[600];
    int nTrans;
    struct TransitionList *transitions;
    int init;
};

struct Transition
{
    struct State *start;
    struct State *end;
    int nPorts;
    struct StringList *ports;
    char *condition;
    int blocked;
    char* add;
};

struct Condition
{
    char port[600];
    char operation;
    char value[600];
};

struct StateList
{
    struct State *state;
    struct StateList *nextState;
};

struct TransitionList
{
    struct Transition *transition;
    struct TransitionList *nextTransition;
};

struct StringList
{
    char *string;
    struct StringList *nextString;
};

struct AutomatoList
{
    struct Automato *automato;
    struct AutomatoList *nextAutomato;
};

struct AutomatoProdList
{
    struct AutomatoProd *automato;
    struct AutomatoProdList *nextAutomato;
};

struct ConditionList
{
    struct Condition *condition;
    struct ConditionList *nextCondition;
};

struct State *newState(char name[20], int init);

void addTransition(struct Transition *transition);

void delState(struct State *state);

struct Automato *newAutomato(char name[600], int lineCount);

void addState(struct State *state, struct Automato *automato);

void delStates(struct Automato *automato);

struct State *findState(struct StateList *states, char name[20]);

void delAutomatoList(struct AutomatoList *automatos);

struct StateList *addStateToList(struct StateList *states, struct State *state);

struct StringList *addString(struct StringList *stringlist, char *string);

struct StringList *delString(struct StringList *stringlist, char *string);

void delStringList(struct StringList *stringList);

struct StringList *cpyStringList(struct StringList *newList, struct StringList *stringList);

struct StringList *concatStringList(struct StringList *firstList, struct StringList *secondList);

struct AutomatoList *addAutomato(struct AutomatoList *automatoList, struct Automato *automato);

struct ConditionList *addConditionToList(struct ConditionList *conditionList, struct Condition *condition);

int existString(struct StringList *list, char *string);

struct StringList *unionStringList(struct StringList *firstList, struct StringList *secondList);

int listLength(struct StringList *list);

void printState(struct State *state);

void printStateList(struct StateList *states);

void printAutomato(struct Automato *automato);

void printsList(struct StringList *list);

void addStateWithoutPorts(struct State *state, struct Automato *automato);

struct AutomatoProd *newAutomatoProd();

void printTransitions(struct TransitionList *transisitions);

void delAutomatoProdList(struct AutomatoProdList *automatos);

void delAutomatoProd(struct AutomatoProd *automato);

struct AutomatoProdList *addAutomatoProd(struct AutomatoProdList *automatoList, struct AutomatoProd *automato);

struct TransitionList *addTransitions(struct TransitionList *transitions, struct TransitionList *newTransitions);

#endif

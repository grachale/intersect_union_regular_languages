# Intersection and union of regular languages.
 Implementation of an algorithm that enables finding the minimal deterministic finite automaton that accepts the intersection or union of languages defined by a pair of finite automata.

The goal is to implement a set of two functions in C++ with the signatures:

DFA unify(const NFA&, const NFA&);
DFA intersect(const NFA&, const NFA&);

Both of these functions must return the minimal automaton for the given language. The input and output of the algorithms are finite automata in the form of structures NFA and DFA. The first structure, NFA, represents a nondeterministic finite automaton (which can also be considered deterministic for some transition functions). The second structure, DFA, represents only a deterministic finite automaton. These structures are simple data structures that maintain data representing the automaton and do not perform any validity checks on the content. The correct initialization and filling with content are the responsibility of the one who creates them.

These structures are defined in the testing environment (so do not define them in your task). For simplicity, the states are defined as values of type unsigned and alphabet symbols as values of type uint8_t.

It is guaranteed that the input of the functions unify and intersect will be valid nondeterministic finite automata. They will meet the following properties:

Sets of states (NFA::m_States) and alphabet symbols (NFA::m_Alphabet) will not be empty.

Initial and final states (NFA::m_InitialState and NFA::m_FinalStates) will be elements of the set of states NFA::m_States.

If there is no defined transition for a state q and an alphabet symbol a in the automaton, then the key (q, a) will not exist in NFA::m_Transitions at all.

The transition table NFA::m_Transitions will also contain only symbols and states specified in the set of alphabet symbols and the set of states.

Comparison of automata with the reference result is performed by testing the isomorphism of transition functions of minimal deterministic finite automata and sets of final states. Your output may differ from the reference only in the naming of states, otherwise it will be evaluated as incorrect. The resulting DFA must also satisfy the conditions of the automaton definition, i.e., the same conditions as for NFA (except for obvious changes due to different definitions of the transition function).

If the result is an automaton that accepts the empty language, it is necessary to submit a single-state automaton with the unchanged alphabet, an empty set of transitions, and final states (see one of the tests in the sample file). It may also happen that both input automata have different alphabets. In this case, we expect the result to be an automaton over the union of these alphabets.

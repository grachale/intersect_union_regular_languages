#ifndef __PROGTEST__

#include <algorithm>
#include <cassert>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <deque>
#include <functional>
#include <iostream>
#include <list>
#include <map>
#include <memory>
#include <numeric>
#include <optional>
#include <queue>
#include <set>
#include <sstream>
#include <stack>
#include <string>
#include <variant>
#include <vector>

using State = unsigned int;
using Symbol = uint8_t;

struct NFA {
    std::set<State> m_States;
    std::set<Symbol> m_Alphabet;
    std::map<std::pair<State, Symbol>, std::set<State>> m_Transitions;
    State m_InitialState;
    std::set<State> m_FinalStates;
};

struct DFA {
    std::set<State> m_States;
    std::set<Symbol> m_Alphabet;
    std::map<std::pair<State, Symbol>, State> m_Transitions;
    State m_InitialState;
    std::set<State> m_FinalStates;
};


#endif
using namespace std;

State findMaxOfState ( const std::set<State> & a )
{
    // maximum of all states in a
    State max = *a . begin();
    for ( auto iter = a . begin (); iter != a . end (); ++iter )
    {
        if ( max < *iter )
            max = *iter;
    }
    return max;
}


NFA fullDefined ( const NFA & a )
{
    NFA fullDefinedA;
    fullDefinedA . m_Alphabet = a . m_Alphabet;
    fullDefinedA . m_InitialState = a . m_InitialState;
    fullDefinedA . m_FinalStates = a . m_FinalStates;
    fullDefinedA . m_States = a . m_States;
    fullDefinedA . m_Transitions = a . m_Transitions;
    // states and transitions could change

    // new unique state if NFA is not full defined
    State newState = findMaxOfState ( a . m_States ) + 1;
    bool indicator = false;


    for ( const auto & state : fullDefinedA . m_States )
    {
        for ( const auto & symbol : fullDefinedA . m_Alphabet )
        {
            auto iter = fullDefinedA . m_Transitions . find (pair(state, symbol));
            if ( iter == fullDefinedA . m_Transitions . end() ) // if we didn't find transition with that symbol
            {
                indicator = true;
                fullDefinedA . m_Transitions . insert ( {{ state, symbol }, { newState } } );
            } else if ( iter -> second . empty () )     // if the transition goes nowhere
            {
                iter -> second . emplace ( newState );
                indicator = true;
            }

        }
    }

    // if we had empty transition, we need to add newState and transitions for newState
    if ( indicator )
    {
        // add newState
        fullDefinedA . m_States . emplace ( newState );
        // transitions for newState
        for ( const auto & symbol : fullDefinedA . m_Alphabet )
            fullDefinedA . m_Transitions . insert ( { {newState, symbol}, { newState } } );
    }

    return fullDefinedA;
}

unsigned int uniqueState = 99999991;

class ComparatorForSet
{
public:
    bool operator () (const pair< set<State>, State >& a, const pair< set<State>, State > & b) const
    {
        return a . first < b . first;
    }
};

class ComparatorForSet2
{
public:
    bool operator () (const pair< pair <State, State>, State >& a, const pair< pair <State, State>, State > & b) const
    {
        return a . first < b . first;
    }
};



DFA determenization  ( const NFA & a )
{
    // new names of determenized states
    State counterOfStates = 0;

    DFA determenizedA;
    determenizedA . m_Alphabet = a .m_Alphabet;               // 1)
    determenizedA . m_InitialState = counterOfStates;         // 2)
    determenizedA . m_States .insert( counterOfStates);    // 3)

    // if first state is final state
    auto iter = a . m_FinalStates . find ( a . m_InitialState );
    if ( iter != a . m_FinalStates . end() )
        determenizedA . m_FinalStates . insert ( counterOfStates);


    // our queue
    queue< pair< set<State>, State > > noReadyStates;
    set< pair< set<State>, State >, ComparatorForSet > workingStates;
    // pair -> first - initial state from given one
    set <State> firstState;
    firstState .insert(a . m_InitialState);
    noReadyStates . push ( pair ( firstState, counterOfStates) );
    workingStates . insert (  pair ( firstState, counterOfStates) );


    // while all states are not completed
    while ( !noReadyStates . empty () )
    {
        // getting state from queue
        pair< set<State>, State > ourState = noReadyStates . front();
        noReadyStates . pop();

        // through every symbol of our alphabet
        for ( const auto & symbol : a . m_Alphabet )
        {
            // new renamed State
            counterOfStates++;
            // our new State
            pair< set<State>,  State > newState;
            newState . second = counterOfStates;

            // through every state in our state
            for ( const auto & smallState : ourState . first )
            {
                auto iter = a . m_Transitions . find ( pair ( smallState, symbol) );

                // we found something
                if ( iter != a . m_Transitions . end () )
                {
                    for ( const auto & stateAfterTransition : iter -> second )
                    {
                        newState . first . insert ( stateAfterTransition );
                    }
                }
            }
            // we maybe have new state and transition for that state for certain symbol

            auto iterWorkingStates = workingStates . find ( newState );
            if ( iterWorkingStates == workingStates . end() )
            {

                // if the state is final state
                for ( auto const & maybeFinalState : newState . first )
                {
                    auto iter2 = a . m_FinalStates . find ( maybeFinalState );
                    if ( iter2 != a . m_FinalStates . end() )
                        determenizedA . m_FinalStates . insert ( newState . second );
                }

                // insert into workingStates
                workingStates . insert ( newState );
                // new state
                determenizedA . m_States . insert ( newState . second );
                // insert in queue to find all transitions
                noReadyStates . push ( newState );
                // new transition
                determenizedA . m_Transitions . insert ( { {ourState . second, symbol }, newState . second  } );
            } else {    // that is not new element, we had it already
                // new transition
                determenizedA . m_Transitions . insert ( { {ourState . second, symbol }, iterWorkingStates -> second  } );
            }
        }
    }

    return determenizedA;
}


DFA parellelAlgorithm ( const DFA& a, const DFA& b, bool unify ) {

    DFA newDFA;
    State countOfStates = 0;

    // alphabet
    newDFA . m_Alphabet = a . m_Alphabet;
    // initial state
    newDFA . m_InitialState  = countOfStates;
    // initial state into states
    newDFA . m_States . insert ( countOfStates);
    // initial state maybe to final states
    if ( unify ) // sjednoceni
    {
        if ( a . m_FinalStates . find (  a . m_InitialState ) != a . m_FinalStates . end () || b . m_FinalStates . find ( b.m_InitialState ) != b . m_FinalStates . end () )
            newDFA . m_FinalStates . insert ( countOfStates );

    } else {   // prunik
        if ( a . m_FinalStates . find ( a.m_InitialState ) != a . m_FinalStates . end () && b . m_FinalStates . find ( b.m_InitialState ) != b . m_FinalStates . end () )
            newDFA . m_FinalStates . insert ( countOfStates );
    }


    queue< pair < pair < State, State >, State > > unprocessedStates;
    set < pair < pair < State, State >, State >, ComparatorForSet2 > allStates;            // ( (stateA, stateB ), newNameState )

    // initial state, GO FOR WORK!!!
    unprocessedStates . push ( { { a . m_InitialState, b . m_InitialState }, countOfStates });
    allStates . insert ( { { a . m_InitialState, b . m_InitialState }, countOfStates });

    while ( !unprocessedStates . empty () )
    {
        auto unprocessedState = unprocessedStates . front ();
        unprocessedStates . pop ();

        for ( const auto & symbol : newDFA . m_Alphabet )
        {
            countOfStates++;
            State transitionA = a . m_Transitions . find ( { unprocessedState . first . first, symbol } ) -> second;
            State transitionB = b . m_Transitions . find ( { unprocessedState . first . second, symbol } ) -> second;

            auto newState = make_pair ( make_pair (  transitionA, transitionB ), countOfStates);

            auto iter = allStates . find ( newState );
            // we didn't find
            if ( iter == allStates . end () )
            {
                // insert into allStates
                allStates . insert ( newState );
                // insert into unprocessedStates
                unprocessedStates . push ( newState );
                // add transition
                newDFA . m_Transitions . insert ( { { unprocessedState . second, symbol }, newState.  second } );
                // newState
                newDFA . m_States . insert ( newState . second  );
                // isItFinalState
                if ( unify ) // sjednoceni
                {
                    if ( a . m_FinalStates . find ( transitionA ) != a . m_FinalStates . end () || b . m_FinalStates . find ( transitionB ) != b . m_FinalStates . end () )
                        newDFA . m_FinalStates . insert ( newState . second );

                } else {   // prunik
                    if ( a . m_FinalStates . find ( transitionA ) != a . m_FinalStates . end () && b . m_FinalStates . find ( transitionB ) != b . m_FinalStates . end () )
                        newDFA . m_FinalStates . insert ( newState . second );
                }
            } else
            {
                // add transition
                newDFA . m_Transitions . insert ( {{unprocessedState . second, symbol }, iter -> second } );

             }
        }
    }

    return newDFA;
}


DFA removeReduntantStates ( const DFA & a ) {
    set<State> copyOfAllState = a . m_States;
    // initial and final states are not reduntant
    set<State> nonReduntantStates = a . m_FinalStates;

    for (const auto &finalState: a.m_FinalStates)
        copyOfAllState.erase(finalState);

    bool indicator = true;
    while (indicator)
    {
        indicator = false;
        auto state = copyOfAllState . begin ();
        while (  state != copyOfAllState . end () )
        {
            bool indicator2 = false;
            for (const auto &symbol: a.m_Alphabet)
            {
                auto iter = nonReduntantStates.find(a . m_Transitions . find({*state, symbol}) -> second );

                if (iter != nonReduntantStates.end() )
                {
                    indicator2 = true;
                    indicator = true;
                    nonReduntantStates.insert(*state);
                    auto toDelete = state;
                    ++state;
                    copyOfAllState.erase(toDelete);
                    break;
                }
            }
            if ( !indicator2 )
                ++state;

        }

    }

    nonReduntantStates . insert ( a . m_InitialState );

    DFA dfaWithoutReduntantStates;
    dfaWithoutReduntantStates . m_Alphabet = a . m_Alphabet;
    dfaWithoutReduntantStates . m_FinalStates = a . m_FinalStates;
    dfaWithoutReduntantStates . m_InitialState = a . m_InitialState;
    dfaWithoutReduntantStates . m_States = nonReduntantStates;

    if ( dfaWithoutReduntantStates . m_States . size() == 1 )
    {
        for ( const auto & state : dfaWithoutReduntantStates . m_States ) {
            for (const auto &symbol: a.m_Alphabet) {
                dfaWithoutReduntantStates.m_Transitions.insert({{state, symbol}, uniqueState});
            }
        }

    } else {
        for ( const auto & state : dfaWithoutReduntantStates . m_States )
        {
            for ( const auto & symbol : a .m_Alphabet )
            {
                auto iter = a . m_Transitions . find ({state, symbol});
                auto iter2 = nonReduntantStates . find (iter -> second );
                // it is reduntant State
                if ( iter2 == nonReduntantStates . end () )
                    dfaWithoutReduntantStates . m_Transitions . insert ( {{state, symbol  }, uniqueState });
                else
                    dfaWithoutReduntantStates . m_Transitions . insert ( {{state, symbol  }, iter -> second });
            }

        }
    }


    return dfaWithoutReduntantStates;
}


DFA removeEquivalentState ( const DFA & a )
{
    DFA withoutEquivalentState;
    withoutEquivalentState . m_Alphabet = a . m_Alphabet;
    withoutEquivalentState . m_InitialState = a . m_InitialState;

    map< pair < pair < State, State >, Symbol >, State > firstEquiv;            // first is original
    vector < pair < State, State > > firstEquivVector, secondEquivVector;
    map < State, State > newName;
    newName . insert ({uniqueState, uniqueState });
    int sizeOfAlphabet = a . m_Alphabet . size();

    // separating for groups

    // start Group
    set < State > groupsStart;
    State firstNotFinalState = uniqueState;
    for ( const auto & state : a . m_States )
    {
        auto iter = a . m_FinalStates . find ( state );
        // it is not final
        if ( iter == a . m_FinalStates . end () )
        {
            firstNotFinalState = state;
            groupsStart . insert ( firstNotFinalState );
            break;
        }
    }


    // end group
    set < State > groupsEnd;
    State firstFinalState;
    if ( a . m_FinalStates . size () > 0 )
    {
         firstFinalState = *a . m_FinalStates . begin ();
         groupsEnd . insert ( firstFinalState );
    }




    // firstEquivVector
    for ( const auto & state : a . m_States )
    {
        auto iter = a . m_FinalStates . find ( state );
        // final state
        if (iter != a . m_FinalStates . end () )
        {
            firstEquivVector . emplace_back ( state, firstFinalState );
            secondEquivVector . emplace_back ( make_pair ( state, firstFinalState ) );
            newName . insert ( {state, firstFinalState} );
        } else { // initial or just state
            firstEquivVector . emplace_back ( make_pair ( state, firstNotFinalState ) );
            secondEquivVector . emplace_back ( make_pair ( state, firstNotFinalState ) );
            newName . insert ( {state, firstNotFinalState} );
        }
    }


    // firstEquiv
    for ( const auto & state : firstEquivVector )
    {
        for ( const auto & symbol : a . m_Alphabet )
        {
            auto iter = a . m_Transitions . find ({state . first, symbol});
            if (iter != a . m_Transitions . end() )
            {
                if ( iter -> second == uniqueState )
                    firstEquiv . insert ( {{state, symbol }, uniqueState } );
                else
                    firstEquiv . insert ( {{state, symbol }, newName . find ( iter -> second ) -> second } );
            }
        }
    }



    bool indicator = true;

    while ( indicator )
    {
        indicator = false;

        int i = 0;
        // comparing firstEquivVector with secondEquivVector
        for ( auto & stateFirst : firstEquivVector )
        {
            for ( const auto & symbol : a . m_Alphabet )
            {
                auto transitionForState = firstEquiv . find ( {stateFirst, symbol });        // transition for renamed state
                auto transitionForGroupState = firstEquiv . find ( { {stateFirst . second, stateFirst . second}, symbol }); // transition of original state of this group
                // they are not equal
                if ( transitionForState -> second != transitionForGroupState -> second )
                {
                    indicator = true;

                    bool haveWeFoundGroup = false;
                    // is it from ends group or from start
                    auto isItInEnd = groupsEnd . find ( stateFirst . second );
                    // it is from end group
                    if ( isItInEnd != groupsEnd . end () )
                    {
                        for ( const auto & stateEndGroup : groupsEnd )
                        {
                            int countOfMatches = 0;
                            for ( const auto & symbol2 : a . m_Alphabet )
                            {
                                auto transitionForStateEnd = firstEquiv . find ({{stateEndGroup, stateEndGroup}, symbol2});
                                auto transitionForOurState = firstEquiv . find ({stateFirst, symbol2});
                                if ( transitionForOurState -> second != transitionForStateEnd -> second ){
                                    break;
                                } else {
                                    ++countOfMatches;
                                }
                            }
                            if ( countOfMatches == sizeOfAlphabet ) {
                                secondEquivVector[i] = {stateFirst . first ,stateEndGroup};
                                auto iterName = newName . find(stateFirst . first);
                                newName . erase (iterName);
                                newName . insert ( { stateFirst . first, stateEndGroup });
                                haveWeFoundGroup = true;
                                break;
                            }
                        }
                    } else { // it is from start group
                        for ( const auto & stateStartGroup : groupsStart )
                        {
                            int countOfMatches = 0;
                            for ( const auto & symbol2 : a . m_Alphabet )
                            {
                                auto transitionForStateEnd = firstEquiv . find ({{stateStartGroup, stateStartGroup}, symbol2});
                                auto transitionForOurState = firstEquiv . find ({stateFirst, symbol2});
                                if ( transitionForOurState -> second != transitionForStateEnd -> second ){
                                    break;
                                } else {
                                    ++countOfMatches;
                                }
                            }
                            if ( countOfMatches == sizeOfAlphabet ) {
                                secondEquivVector[i] = {stateFirst . first ,stateStartGroup};
                                auto iterName = newName . find(stateFirst . first);
                                newName . erase (iterName);
                                newName . insert ( { stateFirst . first, stateStartGroup });
                                haveWeFoundGroup = true;
                                break;
                            }
                        }
                    }

                    if ( !haveWeFoundGroup )
                    {
                        secondEquivVector[i] = {stateFirst . first, stateFirst . first};
                        auto iterName = newName . find (stateFirst .first );
                        newName . erase (iterName);
                        newName . insert ( { stateFirst . first, stateFirst . first });
                        // it is from end group
                        if ( isItInEnd != groupsEnd . end () )
                        {
                            groupsEnd . insert ( stateFirst . first );
                        } else {
                            groupsStart . insert ( stateFirst . first );
                        }
                        for ( const auto & symbol3 : a . m_Alphabet ){
                            auto iterToDelete = firstEquiv . find ( {stateFirst, symbol3 });
                            auto ourTransition = iterToDelete -> second;
                            firstEquiv . erase ( iterToDelete );
                            firstEquiv . insert ({{{stateFirst . first, stateFirst .first}, symbol3}, ourTransition } );
                        }
                    }
                    break;
                }
            }
            // move to the next state
            ++i;
        }
        map< pair < pair < State, State >, Symbol >, State > secondEquiv;

        // change firstEquiv
        for ( const auto & state : secondEquivVector )
        {
            for ( const auto & symbol : a . m_Alphabet )
            {
                secondEquiv . insert ( {{state, symbol }, newName . find ( a . m_Transitions . find ({state . first, symbol}) -> second ) -> second } );
            }
        }
        firstEquivVector = secondEquivVector;
        firstEquiv = secondEquiv;
    }

     withoutEquivalentState . m_FinalStates = groupsEnd;
    for ( const auto & newState : firstEquivVector )
        withoutEquivalentState . m_States . insert ( newState . second );

    for ( const auto & state : withoutEquivalentState . m_States )
        for ( const auto & symbol : withoutEquivalentState . m_Alphabet )
        {
            auto iter = firstEquiv . find ( {{state, state}, symbol} );
            if ( iter -> second != uniqueState )
                withoutEquivalentState . m_Transitions . insert ( { { state, symbol }, iter -> second });
        }

    return withoutEquivalentState;
}



DFA unify(const NFA& a, const NFA& b)
{
    // copies of input NFA
    NFA copyOfA = a;
    NFA copyOfB = b;

    // unify of alphabets
    for ( const auto & symbol : copyOfA . m_Alphabet )
        copyOfB . m_Alphabet . insert ( symbol );
    for ( const auto & symbol : copyOfB . m_Alphabet )
        copyOfA . m_Alphabet . insert ( symbol );

    // full Defined and Determinized
    DFA determinizedA = determenization(fullDefined(copyOfA));
    DFA determinizedB = determenization(fullDefined(copyOfB));

    DFA unifiedDFA = removeEquivalentState(removeReduntantStates ( parellelAlgorithm ( determinizedA, determinizedB, 1 ) ) );


    return unifiedDFA;
}

DFA intersect(const NFA& a, const NFA& b)
{
    // copies of input NFA
    NFA copyOfA = a;
    NFA copyOfB = b;

    // unify of alphabets
    for ( const auto & symbol : copyOfA . m_Alphabet )
        copyOfB . m_Alphabet . insert ( symbol );
    for ( const auto & symbol : copyOfB . m_Alphabet )
        copyOfA . m_Alphabet . insert ( symbol );

    // full Defined and Determinized
    DFA determinizedA = determenization(fullDefined(copyOfA));
    DFA determinizedB = determenization(fullDefined(copyOfB));

    DFA intersectedDFA = removeEquivalentState( removeReduntantStates(parellelAlgorithm ( determinizedA, determinizedB, 0 )) );

    return intersectedDFA;
}


#ifndef __PROGTEST__

// You may need to update this function or the sample data if your state naming strategy differs.
bool operator==(const DFA& a, const DFA& b)
{
    return std::tie(a.m_States, a.m_Alphabet, a.m_Transitions, a.m_InitialState, a.m_FinalStates) == std::tie(b.m_States, b.m_Alphabet, b.m_Transitions, b.m_InitialState, b.m_FinalStates);
}
bool operator==(const NFA& a, const NFA& b)
{
    return std::tie(a.m_States, a.m_Alphabet, a.m_Transitions, a.m_InitialState, a.m_FinalStates) == std::tie(b.m_States, b.m_Alphabet, b.m_Transitions, b.m_InitialState, b.m_FinalStates);
}





int main()
{



    NFA abc {
            {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107} ,
            {'E','Q','9'},
            {
                    {{0,'E'},{103}},
                    {{0,'Q'},{52}},
                    {{0,'9'},{15}},
                    {{1,'E'},{24}},
                    {{1,'Q'},{10}},
                    {{2,'E'},{62}},
                    {{2,'Q'},{60}},
                    {{2,'9'},{1}},
                    {{3,'E'},{97}},
                    {{3,'Q'},{62}},
                    {{3,'9'},{49}},
                    {{5,'E'},{66}},
                    {{6,'9'},{40}},
                    {{7,'E'},{47}},
                    {{7,'Q'},{15}},
                    {{7,'9'},{11}},
                    {{8,'E'},{1}},
                    {{8,'Q'},{83}},
                    {{8,'9'},{5}},
                    {{9,'Q'},{30}},
                    {{10,'E'},{89}},
                    {{10,'Q'},{100}},
                    {{10,'9'},{107}},
                    {{11,'Q'},{3}},
                    {{12,'E'},{9}},
                    {{12,'Q'},{87}},
                    {{12,'9'},{38}},
                    {{13,'E'},{17}},
                    {{13,'Q'},{61}},
                    {{13,'9'},{97}},
                    {{14,'E'},{48}},
                    {{14,'Q'},{33}},
                    {{14,'9'},{28}},
                    {{15,'Q'},{62}},
                    {{16,'Q'},{24}},
                    {{16,'9'},{45}},
                    {{17,'Q'},{23}},
                    {{17,'9'},{90}},
                    {{19,'E'},{81}},
                    {{19,'Q'},{9}},
                    {{19,'9'},{31}},
                    {{20,'E'},{65}},
                    {{20,'9'},{8}},
                    {{22,'E'},{76}},
                    {{22,'Q'},{63}},
                    {{22,'9'},{77}},
                    {{23,'E'},{34}},
                    {{23,'9'},{65}},
                    {{26,'E'},{71}},
                    {{26,'Q'},{50}},
                    {{26,'9'},{11}},
                    {{27,'Q'},{63}},
                    {{27,'9'},{94}},
                    {{28,'E'},{7}},
                    {{28,'Q'},{21}},
                    {{28,'9'},{80}},
                    {{29,'E'},{16}},
                    {{29,'Q'},{26}},
                    {{29,'9'},{77}},
                    {{30,'9'},{15}},
                    {{32,'E'},{60}},
                    {{32,'9'},{20}},
                    {{33,'E'},{25}},
                    {{33,'Q'},{107}},
                    {{33,'9'},{37}},
                    {{35,'E'},{31}},
                    {{35,'Q'},{42}},
                    {{35,'9'},{45}},
                    {{36,'E'},{65}},
                    {{36,'9'},{65}},
                    {{37,'E'},{36}},
                    {{39,'E'},{106}},
                    {{39,'Q'},{103}},
                    {{39,'9'},{65}},
                    {{40,'Q'},{62}},
                    {{41,'E'},{4}},
                    {{41,'Q'},{63}},
                    {{41,'9'},{77}},
                    {{42,'E'},{30}},
                    {{42,'9'},{91}},
                    {{43,'E'},{69}},
                    {{43,'Q'},{87}},
                    {{43,'9'},{49}},
                    {{44,'E'},{34}},
                    {{45,'E'},{85}},
                    {{45,'Q'},{91}},
                    {{45,'9'},{6}},
                    {{46,'E'},{102}},
                    {{46,'Q'},{8}},
                    {{46,'9'},{43}},
                    {{47,'9'},{100}},
                    {{48,'E'},{74}},
                    {{48,'Q'},{86}},
                    {{48,'9'},{17}},
                    {{51,'E'},{8}},
                    {{51,'Q'},{41}},
                    {{51,'9'},{46}},
                    {{52,'9'},{65}},
                    {{53,'9'},{28}},
                    {{54,'E'},{58}},
                    {{54,'Q'},{97}},
                    {{54,'9'},{56}},
                    {{55,'Q'},{72}},
                    {{55,'9'},{66}},
                    {{56,'Q'},{55}},
                    {{57,'9'},{19}},
                    {{58,'E'},{17}},
                    {{58,'Q'},{30}},
                    {{59,'E'},{55}},
                    {{59,'9'},{59}},
                    {{61,'E'},{79}},
                    {{63,'E'},{62}},
                    {{64,'9'},{65}},
                    {{65,'E'},{65}},
                    {{65,'9'},{79}},
                    {{68,'E'},{94}},
                    {{69,'E'},{9}},
                    {{69,'Q'},{87}},
                    {{69,'9'},{103}},
                    {{70,'9'},{74}},
                    {{71,'E'},{34}},
                    {{71,'9'},{65}},
                    {{72,'E'},{62}},
                    {{73,'E'},{17}},
                    {{73,'Q'},{84}},
                    {{73,'9'},{64}},
                    {{74,'E'},{81}},
                    {{74,'Q'},{9}},
                    {{74,'9'},{31}},
                    {{75,'9'},{65}},
                    {{76,'E'},{17}},
                    {{76,'Q'},{84}},
                    {{76,'9'},{64}},
                    {{77,'E'},{103}},
                    {{77,'Q'},{52}},
                    {{77,'9'},{15}},
                    {{78,'E'},{48}},
                    {{78,'Q'},{33}},
                    {{78,'9'},{28}},
                    {{80,'Q'},{62}},
                    {{81,'E'},{8}},
                    {{81,'Q'},{41}},
                    {{81,'9'},{46}},
                    {{82,'E'},{34}},
                    {{82,'9'},{65}},
                    {{83,'E'},{34}},
                    {{84,'E'},{79}},
                    {{85,'E'},{60}},
                    {{85,'9'},{89}},
                    {{86,'E'},{16}},
                    {{86,'Q'},{104}},
                    {{86,'9'},{0}},
                    {{87,'E'},{89}},
                    {{87,'Q'},{100}},
                    {{87,'9'},{107}},
                    {{88,'E'},{81}},
                    {{88,'Q'},{9}},
                    {{88,'9'},{31}},
                    {{89,'E'},{65}},
                    {{89,'9'},{8}},
                    {{90,'E'},{73}},
                    {{90,'Q'},{63}},
                    {{90,'9'},{77}},
                    {{91,'E'},{62}},
                    {{91,'Q'},{60}},
                    {{91,'9'},{1}},
                    {{92,'E'},{7}},
                    {{92,'Q'},{21}},
                    {{92,'9'},{96}},
                    {{93,'E'},{47}},
                    {{93,'Q'},{15}},
                    {{93,'9'},{11}},
                    {{95,'E'},{66}},
                    {{96,'Q'},{62}},
                    {{97,'9'},{65}},
                    {{98,'E'},{94}},
                    {{99,'E'},{32}},
                    {{99,'Q'},{2}},
                    {{99,'9'},{6}},
                    {{100,'Q'},{63}},
                    {{100,'9'},{66}},
                    {{101,'E'},{9}},
                    {{101,'Q'},{87}},
                    {{101,'9'},{38}},
                    {{104,'E'},{23}},
                    {{104,'Q'},{67}},
                    {{104,'9'},{11}},
                    {{105,'E'},{58}},
                    {{105,'Q'},{75}},
                    {{105,'9'},{56}},
                    {{106,'E'},{31}},
                    {{106,'Q'},{42}},
                    {{106,'9'},{45}},
                    {{107,'E'},{106}},
                    {{107,'Q'},{103}},
                    {{107,'9'},{65}},
            },
            14 ,
            {0, 2, 3, 4, 5, 6, 9, 13, 14, 15, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 31, 33, 34, 35, 37, 40, 41, 43, 46, 47, 49, 52, 53, 55, 57, 59, 68, 70, 71, 73, 74, 76, 77, 78, 80, 82, 86, 88, 89, 90, 91, 92, 95, 96, 98, 100, 104, 106}
    };

    NFA xyz {
            {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112} ,
            {'E','Q','9'},
            {
                    {{0,'E'},{5}},
                    {{1,'E'},{83}},
                    {{1,'Q'},{64}},
                    {{2,'E'},{62}},
                    {{3,'E'},{32}},
                    {{3,'Q'},{41}},
                    {{3,'9'},{16}},
                    {{4,'E'},{104}},
                    {{4,'Q'},{83}},
                    {{4,'9'},{10}},
                    {{5,'E'},{74}},
                    {{5,'Q'},{65}},
                    {{5,'9'},{63}},
                    {{7,'E'},{21}},
                    {{7,'Q'},{81}},
                    {{9,'Q'},{66}},
                    {{10,'E'},{25}},
                    {{10,'Q'},{103}},
                    {{10,'9'},{40}},
                    {{12,'E'},{65}},
                    {{12,'Q'},{65}},
                    {{13,'Q'},{20}},
                    {{13,'9'},{65}},
                    {{14,'E'},{63}},
                    {{15,'E'},{77}},
                    {{15,'Q'},{62}},
                    {{15,'9'},{45}},
                    {{16,'E'},{61}},
                    {{16,'Q'},{16}},
                    {{16,'9'},{16}},
                    {{17,'9'},{77}},
                    {{18,'E'},{52}},
                    {{19,'E'},{110}},
                    {{19,'Q'},{0}},
                    {{19,'9'},{3}},
                    {{20,'E'},{33}},
                    {{20,'Q'},{0}},
                    {{20,'9'},{112}},
                    {{22,'E'},{49}},
                    {{22,'Q'},{70}},
                    {{22,'9'},{11}},
                    {{23,'E'},{24}},
                    {{23,'Q'},{20}},
                    {{24,'E'},{61}},
                    {{25,'E'},{14}},
                    {{25,'9'},{106}},
                    {{27,'E'},{11}},
                    {{27,'Q'},{15}},
                    {{27,'9'},{8}},
                    {{28,'Q'},{68}},
                    {{28,'9'},{75}},
                    {{29,'E'},{1}},
                    {{29,'Q'},{16}},
                    {{29,'9'},{32}},
                    {{30,'E'},{44}},
                    {{30,'Q'},{39}},
                    {{30,'9'},{50}},
                    {{31,'E'},{11}},
                    {{31,'Q'},{63}},
                    {{32,'E'},{31}},
                    {{32,'Q'},{28}},
                    {{32,'9'},{78}},
                    {{34,'E'},{52}},
                    {{34,'Q'},{5}},
                    {{35,'E'},{27}},
                    {{35,'Q'},{46}},
                    {{35,'9'},{22}},
                    {{36,'E'},{15}},
                    {{36,'Q'},{19}},
                    {{36,'9'},{48}},
                    {{37,'E'},{71}},
                    {{38,'E'},{14}},
                    {{38,'Q'},{2}},
                    {{38,'9'},{61}},
                    {{39,'Q'},{64}},
                    {{41,'E'},{8}},
                    {{41,'Q'},{68}},
                    {{41,'9'},{98}},
                    {{43,'E'},{21}},
                    {{43,'Q'},{71}},
                    {{43,'9'},{38}},
                    {{44,'E'},{107}},
                    {{44,'9'},{106}},
                    {{45,'E'},{28}},
                    {{45,'Q'},{35}},
                    {{45,'9'},{103}},
                    {{46,'E'},{102}},
                    {{46,'Q'},{4}},
                    {{46,'9'},{69}},
                    {{47,'E'},{106}},
                    {{48,'E'},{51}},
                    {{48,'Q'},{109}},
                    {{48,'9'},{12}},
                    {{49,'9'},{61}},
                    {{51,'E'},{22}},
                    {{51,'Q'},{17}},
                    {{51,'9'},{34}},
                    {{52,'9'},{25}},
                    {{53,'Q'},{12}},
                    {{54,'Q'},{0}},
                    {{54,'9'},{56}},
                    {{55,'E'},{77}},
                    {{55,'Q'},{0}},
                    {{55,'9'},{56}},
                    {{56,'E'},{59}},
                    {{56,'Q'},{77}},
                    {{57,'Q'},{77}},
                    {{59,'E'},{108}},
                    {{59,'Q'},{38}},
                    {{59,'9'},{53}},
                    {{60,'E'},{56}},
                    {{61,'E'},{61}},
                    {{61,'Q'},{80}},
                    {{61,'9'},{66}},
                    {{64,'E'},{66}},
                    {{66,'Q'},{62}},
                    {{68,'9'},{62}},
                    {{69,'E'},{81}},
                    {{69,'Q'},{71}},
                    {{69,'9'},{38}},
                    {{70,'E'},{81}},
                    {{70,'Q'},{81}},
                    {{71,'E'},{44}},
                    {{71,'Q'},{39}},
                    {{71,'9'},{93}},
                    {{72,'E'},{108}},
                    {{72,'Q'},{38}},
                    {{72,'9'},{53}},
                    {{73,'E'},{77}},
                    {{73,'Q'},{100}},
                    {{73,'9'},{102}},
                    {{76,'E'},{110}},
                    {{76,'Q'},{0}},
                    {{76,'9'},{3}},
                    {{77,'Q'},{62}},
                    {{78,'E'},{52}},
                    {{82,'E'},{51}},
                    {{82,'Q'},{109}},
                    {{82,'9'},{12}},
                    {{83,'E'},{15}},
                    {{83,'Q'},{76}},
                    {{83,'9'},{82}},
                    {{84,'E'},{28}},
                    {{84,'Q'},{35}},
                    {{84,'9'},{24}},
                    {{85,'Q'},{66}},
                    {{87,'E'},{25}},
                    {{87,'Q'},{24}},
                    {{87,'9'},{40}},
                    {{89,'E'},{27}},
                    {{89,'Q'},{46}},
                    {{89,'9'},{22}},
                    {{91,'9'},{61}},
                    {{92,'E'},{22}},
                    {{92,'Q'},{17}},
                    {{92,'9'},{34}},
                    {{94,'E'},{11}},
                    {{94,'Q'},{63}},
                    {{95,'E'},{83}},
                    {{95,'Q'},{64}},
                    {{96,'E'},{25}},
                    {{96,'Q'},{24}},
                    {{96,'9'},{40}},
                    {{97,'E'},{9}},
                    {{97,'Q'},{0}},
                    {{97,'9'},{3}},
                    {{98,'E'},{1}},
                    {{98,'Q'},{16}},
                    {{98,'9'},{32}},
                    {{99,'E'},{66}},
                    {{99,'Q'},{100}},
                    {{99,'9'},{84}},
                    {{101,'E'},{30}},
                    {{102,'E'},{28}},
                    {{102,'Q'},{89}},
                    {{102,'9'},{24}},
                    {{103,'E'},{61}},
                    {{104,'E'},{103}},
                    {{104,'Q'},{20}},
                    {{105,'E'},{24}},
                    {{105,'Q'},{20}},
                    {{106,'E'},{71}},
                    {{107,'Q'},{20}},
                    {{107,'9'},{79}},
                    {{108,'E'},{56}},
                    {{110,'Q'},{66}},
                    {{111,'Q'},{0}},
                    {{111,'9'},{56}},
                    {{112,'E'},{37}},
            },
            35 ,
            {0, 1, 7, 16, 17, 22, 24, 27, 31, 32, 33, 34, 36, 39, 41, 43, 44, 47, 50, 51, 54, 55, 56, 59, 60, 69, 70, 72, 83, 92, 93, 94, 95, 103, 108, 111, 112}
    };
    auto boo2 = determenization(fullDefined(xyz));



    NFA a1{
            {0, 1, 2},
            {'a', 'b'},
            {
                    {{0, 'a'}, {0, 1}},
                    {{0, 'b'}, {0}},
                    {{1, 'a'}, {2}},
            },
            0,
            {2},
    };
    NFA a2{
            {0, 1, 2},
            {'a', 'b'},
            {
                    {{0, 'a'}, {1}},
                    {{1, 'a'}, {2}},
                    {{2, 'a'}, {2}},
                    {{2, 'b'}, {2}},
            },
            0,
            {2},
    };
    DFA a{
            {0, 1, 2, 3, 4},
            {'a', 'b'},
            {
                    {{0, 'a'}, {1}},
                    {{1, 'a'}, {2}},
                    {{2, 'a'}, {2}},
                    {{2, 'b'}, {3}},
                    {{3, 'a'}, {4}},
                    {{3, 'b'}, {3}},
                    {{4, 'a'}, {2}},
                    {{4, 'b'}, {3}},
            },
            0,
            {2},
    };
    assert(intersect(a1, a2) == a);

    NFA b1{
            {0, 1, 2, 3, 4},
            {'a', 'b'},
            {
                    {{0, 'a'}, {1}},
                    {{0, 'b'}, {2}},
                    {{2, 'a'}, {2, 3}},
                    {{2, 'b'}, {2}},
                    {{3, 'a'}, {4}},
            },
            0,
            {1, 4},
    };
    NFA b2{
            {0, 1, 2, 3, 4},
            {'a', 'b'},
            {
                    {{0, 'b'}, {1}},
                    {{1, 'a'}, {2}},
                    {{2, 'b'}, {3}},
                    {{3, 'a'}, {4}},
                    {{4, 'a'}, {4}},
                    {{4, 'b'}, {4}},
            },
            0,
            {4},
    };
    DFA b{
            {0, 1, 2, 3, 4, 5, 6, 7, 8},
            {'a', 'b'},
            {
                    {{0, 'a'}, {1}},
                    {{0, 'b'}, {2}},
                    {{2, 'a'}, {3}},
                    {{2, 'b'}, {4}},
                    {{3, 'a'}, {5}},
                    {{3, 'b'}, {6}},
                    {{4, 'a'}, {7}},
                    {{4, 'b'}, {4}},
                    {{5, 'a'}, {5}},
                    {{5, 'b'}, {4}},
                    {{6, 'a'}, {8}},
                    {{6, 'b'}, {4}},
                    {{7, 'a'}, {5}},
                    {{7, 'b'}, {4}},
                    {{8, 'a'}, {8}},
                    {{8, 'b'}, {8}},
            },
            0,
            {1, 5, 8},
    };
    assert(unify(b1, b2) == b);

    NFA c1{
            {0, 1, 2, 3, 4},
            {'a', 'b'},
            {
                    {{0, 'a'}, {1}},
                    {{0, 'b'}, {2}},
                    {{2, 'a'}, {2, 3}},
                    {{2, 'b'}, {2}},
                    {{3, 'a'}, {4}},
            },
            0,
            {1, 4},
    };
    NFA c2{
            {0, 1, 2},
            {'a', 'b'},
            {
                    {{0, 'a'}, {0}},
                    {{0, 'b'}, {0, 1}},
                    {{1, 'b'}, {2}},
            },
            0,
            {2},
    };
    DFA c{
            {0},
            {'a', 'b'},
            {},
            0,
            {},
    };
    assert(intersect(c1, c2) == c);

    NFA d1{
            {0, 1, 2, 3},
            {'i', 'k', 'q'},
            {
                    {{0, 'i'}, {2}},
                    {{0, 'k'}, {1, 2, 3}},
                    {{0, 'q'}, {0, 3}},
                    {{1, 'i'}, {1}},
                    {{1, 'k'}, {0}},
                    {{1, 'q'}, {1, 2, 3}},
                    {{2, 'i'}, {0, 2}},
                    {{3, 'i'}, {3}},
                    {{3, 'k'}, {1, 2}},
            },
            0,
            {2, 3},
    };

    NFA d2{
            {0, 1, 2, 3},
            {'i', 'k'},
            {
                    {{0, 'i'}, {3}},
                    {{0, 'k'}, {1, 2, 3}},
                    {{1, 'k'}, {2}},
                    {{2, 'i'}, {0, 1, 3}},
                    {{2, 'k'}, {0, 1}},
            },
            0,
            {2, 3},
    };
    DFA d{
            {0, 1, 2, 3},
            {'i', 'k', 'q'},
            {
                    {{0, 'i'}, {1}},
                    {{0, 'k'}, {2}},
                    {{2, 'i'}, {3}},
                    {{2, 'k'}, {2}},
                    {{3, 'i'}, {1}},
                    {{3, 'k'}, {2}},
            },
            0,
            {1, 2, 3},
    };

    assert(intersect(d1, d2) == d);
}

#endif

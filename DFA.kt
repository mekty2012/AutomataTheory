class DeterministicFiniteAutomata(val states:Set<Int>, val alphabets:Set<Char>, val transpositions:Map<Pair<Int, Char>, Int>, val initial:Int, val finals:Set<Int>) {
  init {
    if (initial !in states) {
      throw IllegalArgumentException("Initial State not included in states")
    }
    for (final in finals) {
      if (final !in states) {
        throw IllegalArgumentException("Final State $final not included in states")
      }
    }
    for (transposition in transpositions) {
      if (transposition.key.first !in states) {
        throw IllegalArgumentException("Transposition former State ${transposition.key.first} not included in states")
      }
      if (transposition.value !in states) {
        throw IllegalArgumentException("Transposition latter State ${transposition.value} not included in states")
      }
    }
    for (state in states) {
      for (alphabet in alphabets) {
        if (Pair(state, alphabet) !in transpositions.keys) {
          throw IllegalArgumentException("Transposition not deterministic")
        }
      }
    }
  }
  fun accept(s:String):Boolean {
    var state = initial
    for (c in s) {
      if (c !in alphabets) {
        throw IllegalArgumentException("Character $c in input string not in alphabets")
      }
      state = transpositions[Pair(state, c)]!!
    }
    return state in finals
  }
}

fun nfaToDFA(states:Set<Int>, alphabets:Set<Char>, transpositions:Map<Pair<Int, Char>, Set<Int>>, initial:Int, finals:Set<Int>, empty:Char):DeterministicFiniteAutomata {
  if (initial !in states) {
    throw IllegalArgumentException("Initial State not included in states")
  }
  for (final in finals) {
    if (final !in states) {
      throw IllegalArgumentException("Final State $final not included in states")
    }
  }
  for (transposition in transpositions) {
    if (transposition.key.first !in states) {
      throw IllegalArgumentException("Transposition former State ${transposition.key.first} not included in states")
    }
    for (result in transposition.value) {
      if (result !in states) {
        throw IllegalArgumentException("Transposition latter State ${transposition.value} not included in states")
      }
    }
  }
  if (empty in alphabets) {
    throw java.lang.IllegalArgumentException("Empty character must not be in alphabets")
  }
  // create movable steps
  val movableStateMap = mutableMapOf<Int, Set<Int>>()
  for (state in states) {
    var movableStates = setOf<Int>()
    movableStateMap[state] = transpositions.getOrDefault(Pair(state, empty), setOf()).union(setOf(state))
  }
  // find all states and transpositions
  val newStateSetSet = mutableSetOf<Set<Int>>()
  val newTranspositionMap = mutableMapOf<Pair<Set<Int>, Char>, Set<Int>>()
  val stateSetQueue = mutableListOf(setOf(initial))
  while (stateSetQueue.isNotEmpty()) {
    val stateSet = stateSetQueue.removeAt(0)
    for (alphabet in alphabets) {
      var newStateSet = setOf<Int>()
      for (state in stateSet) {
        newStateSet = newStateSet.union(transpositions.getOrDefault(Pair(state, alphabet), setOf()) + state)
      }
      var newNewStateSet = setOf<Int>()
      for (newState in newStateSet) {
        newNewStateSet = newNewStateSet.union(movableStateMap.getOrDefault(newState, setOf(newState)))
      }
      if (newNewStateSet !in newStateSetSet) {
        newStateSetSet.add(newNewStateSet)
        stateSetQueue.add(newNewStateSet)
      }
      newTranspositionMap[Pair(stateSet, alphabet)] = newNewStateSet
    }
  }
  val newStates = mutableMapOf<Set<Int>, Int>()
  val resultTranspositions = mutableMapOf<Pair<Int, Char>, Int>()
  for ((i, newStateSet) in newStateSetSet.withIndex()) {
    newStates[newStateSet] = i
  }
  for (newStateSet in newStateSetSet) {
    for (alphabet in alphabets) {
      resultTranspositions[Pair(newStates[newStateSet]!!, alphabet)] = newStates[newTranspositionMap[Pair(newStateSet, alphabet)]]!!
    }
  }
  val resultState = newStates.values.toSet()
  val resultFinalStates = mutableSetOf<Int>()
  for (entry in newStates) {
    if (entry.key.intersect(finals).isNotEmpty()) {resultFinalStates.add(newStates[entry.key]!!)}
  }
  return DeterministicFiniteAutomata(resultState, alphabets, resultTranspositions, newStates[setOf(initial)]!!, resultFinalStates)
}

fun minimize(dfa:DeterministicFiniteAutomata):DeterministicFiniteAutomata {

  // Remove states that cannot go from initial state
  val stateQueue = mutableListOf(dfa.initial)
  val reachableStates = mutableSetOf(dfa.initial)
  while (stateQueue.isNotEmpty()) {
    val state = stateQueue.removeAt(0)
    for (alphabet in dfa.alphabets) {
      val next = dfa.transpositions[Pair(state, alphabet)]!!
      if (next !in reachableStates) {
        stateQueue.add(next)
        reachableStates.add(next)
      }
    }
  }

  var equivalenceClasses = listOf((reachableStates - dfa.finals).toList(), dfa.finals.toList())

  while (true) {
    val formerSize = equivalenceClasses.size
    val newClasses = mutableListOf<MutableList<Int>>()
    for (equivalenceClass in equivalenceClasses) {
      val newClass = mutableListOf<MutableList<Int>>()
      loop@for (item in equivalenceClass) {
        for (eachClass in newClass) {
          if (nextEqual(item, eachClass[0], equivalenceClasses, dfa)) {
            eachClass.add(item)
            continue@loop
          }
        }
        newClass.add(mutableListOf(item))
      }
      newClasses.addAll(newClass)
    }
    equivalenceClasses = newClasses
    if (equivalenceClasses.size != formerSize) break
  }

  val classMap = mutableMapOf<Int, Int>()
  for ((i, equivalenceClass) in equivalenceClasses.withIndex()) {
    for (item in equivalenceClass) {
      classMap[item] = i
    }
  }

  val resultTranspositions = mutableMapOf<Pair<Int, Char>, Int>()
  for (equivalenceClass in equivalenceClasses) {
    for (alphabet in dfa.alphabets) {
      resultTranspositions[Pair(classMap[equivalenceClass[0]]!!, alphabet)] = classMap[dfa.transpositions[Pair(equivalenceClass[0], alphabet)]]!!
    }
  }
  
  return DeterministicFiniteAutomata(classMap.values.toSet(), dfa.alphabets, resultTranspositions, classMap[dfa.initial]!!, dfa.finals.map{classMap[it]!!}.toSet())
}
fun nextEqual(first:Int, second:Int, eqClass:List<List<Int>>, dfa:DeterministicFiniteAutomata):Boolean {
  var ans = true
  for (alphabet in dfa.alphabets) {
    val nextOfFirst = dfa.transpositions.getValue(first to alphabet)
    val nextOfSecond = dfa.transpositions.getValue(second to alphabet)
    if (eqClass.find{nextOfFirst in it} != eqClass.find{nextOfSecond in it}) {
      ans = false
      break
    }
  }
  return ans
}

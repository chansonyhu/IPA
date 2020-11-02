// This automaton contains the specification for
// LDV driver verification framework.
// It checks only for ERROR labels.

CONTROL AUTOMATON SVCOMP

INITIAL STATE Init;

STATE USEFIRST Init :
  MATCH LABEL [LDV_ERROR] -> ERROR;

END AUTOMATON

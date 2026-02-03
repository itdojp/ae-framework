/* SPIN sample: minimal send/receive with an eventuality property */

chan ch = [0] of { bit };
bool done = false;

active proctype Sender() {
  ch!1;
}

active proctype Receiver() {
  bit x;
  ch?x;
  done = true;
}

/* Eventually, Receiver sets done=true */
ltl p_done { <> done }


------------------------------ MODULE token4s ------------------------------
EXTENDS Integers
CONSTANT N
ASSUME N \in Nat \ {0,1}
Procs == 1..(N-1)
(* Dijkstra's stabilizing 4 state token ring with processes
--algorithm Token4stateRing {
    variable up = [k \in 0..N |-> (k%2)], c = [k \in 0..N |-> (k%2)];
    fair process (j \in Procs)
    { J1: while (TRUE)
        {
        either 
            { await (c[(self-1)] /= c[self]);
                c[self] := c[(self-1)];
                up[self] := 1;  \* TRUE (Representing TRUE as 1 and FALSE as 0)
            }
        or 
            { await ((c[(self+1)] = c[self]) /\ up[(self+1)]=0 /\ up[self]=1);
                up[self] := 0;  \* FALSE
            }
        }
    }
    fair process (i \in {0})
    { I0: up[0] := 1; \* process 0's "up" is always 1
      I1: while (TRUE)
         { await ((c[1] = c[0])/\ up[1]=0);
             c[0] :=  (c[0]+1)%2;
         }
    }
    fair process (z \in {N})
    { Z0: up[self] := 0; \* process N's "up" is always 0
      Z1: while (TRUE)
         { await (c[(N-1)] /= c[N]);
             c[N] := c[(N-1)];
         }
    }
}
*)
\* BEGIN TRANSLATION
VARIABLES up, c, pc

vars == << up, c, pc >>

ProcSet == (Procs) \cup ({0}) \cup ({N})

Init == (* Global variables *)
        /\ up = [k \in 0..N |-> (k%2)]
        /\ c = [k \in 0..N |-> (k%2)]
        /\ pc = [self \in ProcSet |-> CASE self \in Procs -> "J1"
                                        [] self \in {0} -> "I0"
                                        [] self \in {N} -> "Z0"]

J1(self) == /\ pc[self] = "J1"
            /\ \/ /\ (c[(self-1)] /= c[self])
                  /\ c' = [c EXCEPT ![self] = c[(self-1)]]
                  /\ up' = [up EXCEPT ![self] = 1]
               \/ /\ ((c[(self+1)] = c[self]) /\ up[(self+1)]=0 /\ up[self]=1)
                  /\ up' = [up EXCEPT ![self] = 0]
                  /\ c' = c
            /\ pc' = [pc EXCEPT ![self] = "J1"]

j(self) == J1(self)

I0(self) == /\ pc[self] = "I0"
            /\ up' = [up EXCEPT ![0] = 1]
            /\ pc' = [pc EXCEPT ![self] = "I1"]
            /\ c' = c

I1(self) == /\ pc[self] = "I1"
            /\ ((c[1] = c[0])/\ up[1]=0)
            /\ c' = [c EXCEPT ![0] = (c[0]+1)%2]
            /\ pc' = [pc EXCEPT ![self] = "I1"]
            /\ up' = up

i(self) == I0(self) \/ I1(self)

Z0(self) == /\ pc[self] = "Z0"
            /\ up' = [up EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "Z1"]
            /\ c' = c

Z1(self) == /\ pc[self] = "Z1"
            /\ (c[(N-1)] /= c[N])
            /\ c' = [c EXCEPT ![N] = c[(N-1)]]
            /\ pc' = [pc EXCEPT ![self] = "Z1"]
            /\ up' = up

z(self) == Z0(self) \/ Z1(self)

Next == (\E self \in Procs: j(self))
           \/ (\E self \in {0}: i(self))
           \/ (\E self \in {N}: z(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(j(self))
        /\ \A self \in {0} : WF_vars(i(self))
        /\ \A self \in {N} : WF_vars(z(self))

\* END TRANSLATION
InvProp == /\(\A k \in 0..N: c[k] <= 1)
           /\(\A k \in 0..N: up[k] <= 1)
Stabilization == <> InvProp
=============================================================================
\* Modification History
\* Last modified Sun Dec 14 23:45:18 EST 2014 by Siddharth
\* Created Fri Dec 12 03:56:03 EST 2014 by Siddharth
-------------------------------------------------------------------------------
Project submitted by Siddharth Krishna Sinha (ssinha4@buffalo.edu)
-------------------------------------------------------------------------------

-------------------------------- MODULE hlc --------------------------------
EXTENDS Integers
CONSTANT N, STOP, EPSILON
ASSUME N \in Nat \ {0,1}
Procs == 1..N
SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j
(* Hybrid Logical Clocks naive algorithm
--algorithm hlc {
    variable pt = [j \in Procs |-> 0],lc = [j \in Procs |-> 0],mailboxL = [j \in Procs |-> 0],
              mailboxC = [j \in Procs |-> 0],c = [j \in Procs |-> 0],ltmp = 0;
    fair process (j \in Procs){  
        J0: while (pt[self] < STOP){ 
                either \* local or receive event
                J1:{ \* phy clocks cannot diverge more than EPSILON
                    await(\A k \in Procs: pt[self] < pt[k]+ EPSILON);
                    pt[self] := pt[self] + 1;
                    ltmp := lc[self];
                    lc[self] := SetMax({ltmp,mailboxL[self],pt[self]});
                    if((lc[self]=ltmp) \land (lc[self]=mailboxL[self]))
                    { c[self] := SetMax({c[self],mailboxC[self]}) + 1; }
                    else if(lc[self]=ltmp)
                    { c[self] := c[self] + 1; }
                    else if(lc[self]=mailboxL[self])
                    { c[self] := mailboxC[self] + 1; }
                    else
                    { c[self] := 0; }
                    ;
                }
                or \* send event
                J2:{ \* phy clocks cannot diverge more than EPSILON
                    await(\A k \in Procs: pt[self] < pt[k]+ EPSILON);
                    pt[self] := pt[self] + 1;
                    ltmp := lc[self];
                    lc[self] := SetMax({ltmp,pt[self]});
                    if(lc[self]=ltmp)
                    { c[self] := c[self] + 1; }
                    else
                    { c[self] := 0; }
                    ;
                    mailboxL[(self%N)+1] :=  lc[self];
                    mailboxC[(self%N)+1] :=  c[self];
                }
            }
    }
}
*)
\* BEGIN TRANSLATION
VARIABLES pt, lc, mailboxL, mailboxC, c, ltmp, pc

vars == << pt, lc, mailboxL, mailboxC, c, ltmp, pc >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ pt = [j \in Procs |-> 0]
        /\ lc = [j \in Procs |-> 0]
        /\ mailboxL = [j \in Procs |-> 0]
        /\ mailboxC = [j \in Procs |-> 0]
        /\ c = [j \in Procs |-> 0]
        /\ ltmp = 0
        /\ pc = [self \in ProcSet |-> "J0"]

J0(self) == /\ pc[self] = "J0"
            /\ IF pt[self] < STOP
                  THEN /\ \/ /\ pc' = [pc EXCEPT ![self] = "J1"]
                          \/ /\ pc' = [pc EXCEPT ![self] = "J2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << pt, lc, mailboxL, mailboxC, c, ltmp >>

J1(self) == /\ pc[self] = "J1"
            /\ (\A k \in Procs: pt[self] < pt[k]+ EPSILON)
            /\ pt' = [pt EXCEPT ![self] = pt[self] + 1]
            /\ ltmp' = lc[self]
            /\ lc' = [lc EXCEPT ![self] = SetMax({ltmp',mailboxL[self],pt'[self]})]
            /\ IF (lc'[self]=ltmp') \land (lc'[self]=mailboxL[self])
                  THEN /\ c' = [c EXCEPT ![self] = SetMax({c[self],mailboxC[self]}) + 1]
                  ELSE /\ IF lc'[self]=ltmp'
                             THEN /\ c' = [c EXCEPT ![self] = c[self] + 1]
                             ELSE /\ IF lc'[self]=mailboxL[self]
                                        THEN /\ c' = [c EXCEPT ![self] = mailboxC[self] + 1]
                                        ELSE /\ c' = [c EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "J0"]
            /\ UNCHANGED << mailboxL, mailboxC >>

J2(self) == /\ pc[self] = "J2"
            /\ (\A k \in Procs: pt[self] < pt[k]+ EPSILON)
            /\ pt' = [pt EXCEPT ![self] = pt[self] + 1]
            /\ ltmp' = lc[self]
            /\ lc' = [lc EXCEPT ![self] = SetMax({ltmp',pt'[self]})]
            /\ IF lc'[self]=ltmp'
                  THEN /\ c' = [c EXCEPT ![self] = c[self] + 1]
                  ELSE /\ c' = [c EXCEPT ![self] = 0]
            /\ mailboxL' = [mailboxL EXCEPT ![(self%N)+1] = lc'[self]]
            /\ mailboxC' = [mailboxC EXCEPT ![(self%N)+1] = c'[self]]
            /\ pc' = [pc EXCEPT ![self] = "J0"]

j(self) == J0(self) \/ J1(self) \/ J2(self)

Next == (\E self \in Procs: j(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(j(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

TypeOK == (\A k \in Procs: lc[k] >= pt[k])
Sync == (\A k,l \in Procs: pt[k] <= pt[l]+EPSILON)
Bounded == (\A k \in Procs: lc[k] < pt[k] + N*(EPSILON+1))
BoundedC == (\A k \in Procs: c[k] <= N*(EPSILON+1))

=============================================================================
\* Modification History
\* Last modified Thu Oct 30 22:56:28 EDT 2014 by Siddharth
\* Created Thu Oct 30 21:04:25 EDT 2014 by Siddharth
This is the implementation of the HLC. 
Here we model check to prove the boundedness, which in the case of naive algorithm was divergent. 
We also model check that c is bounded. 
-------------------------------------------------------------------------------
Project submitted by Siddharth Krishna Sinha (ssinha4@buffalo.edu)
-------------------------------------------------------------------------------

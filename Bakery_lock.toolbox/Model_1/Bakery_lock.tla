---------------------------- MODULE Bakery_lock ----------------------------
EXTENDS Integers, Sequences
CONSTANT N, MaxTokenNumber

(*--algorithm Bakery 

variables choosing = [x \in 1..N |-> FALSE]; label = [x \in 1..N |-> 0];
        lessLessProcResult = [x \in 1..N |-> FALSE]; maxProcResult = [x \in 1..N |-> 0];

procedure NonCriticalSection()
    variables isEndless;
begin
    nonCritical0: with x \in {0,1} do
              isEndless := x;
          end with;
    nonCritical1: if (isEndless = 1) then
              nonCritical2: while (TRUE) do
                  nonCritical3: skip;
              end while;
          else 
              nonCritical4: return;
          end if;
end procedure;

procedure lessless(i, j) 
    variables labelI, labelJ;
begin
    ll1: labelI := label[i];
    ll2: labelJ := label[j];
        ll3: if (labelI < labelJ) then
                 lessLessProcResult[i] := TRUE;
                 return;
             end if;
        ll4: if (labelI = labelJ /\ i < j) then
                 lessLessProcResult[i] := TRUE;
                 return;
             end if;
        ll5: lessLessProcResult[i] := FALSE; 
             return;
end procedure;

procedure max() 
    variables m = -1; k = 1; temp;
begin
    max1: while (k <= N) do
        max2: temp := label[k];
        max3:
        if (temp > m) then
            m := temp;
        end if;
        k := k+1;     
    end while;
    max4: maxProcResult[self] := m;
    max5: return;  
end procedure;

procedure wait(i, j) 
    variables labelI; labelJ;
begin
    wait1: while (TRUE) do
        wait2: labelI := label[i];
        wait3: labelJ := label[j];
        wait4: call lessless(i, j);
        wait5: 
        if (labelJ = 0 \/ lessLessProcResult[i] = TRUE) then
            wait6: return;
        end if;
    end while;
end procedure;

process Proc \in 1..N 
    variables i = self; j; otherprocesses;
begin
    p0: while (TRUE) do
        p1: call NonCriticalSection(); 
        p2: choosing[i] := TRUE;
        p3a: call max();                 
        \* limitation of tokens number is artificial, but it is neccessary, 
        \* because otherwise the number of different states is infinite 
        p3b: if (maxProcResult[self] >= MaxTokenNumber) then
        \* After next line: label[i] = MaxTokenNumber
        maxProcResult[self] := MaxTokenNumber-1;
        end if;
        p3c: label[i] := 1 + maxProcResult[self];
        p4: choosing[self] := FALSE;
        p5a: otherprocesses := 1..N \ {i};
        p5b:
        while (otherprocesses # {}) do
            with proc \in otherprocesses do
                j := proc;
            end with;
            otherprocesses := otherprocesses \ {j};
            p6: await choosing[j] = FALSE;
            \* await (label[j] = 0) \/ (label[i] << label[j]) 
            p7: call wait(i,j);
        end while;
        criticalSection: skip;
        p9: label[i] := 0; 
    end while;
end process;

end algorithm --*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-63667a3b9bd129de0e65a66268c041c2
\* Process variable i of process Proc at line 72 col 15 changed to i_
\* Process variable j of process Proc at line 72 col 25 changed to j_
\* Procedure variable labelI of procedure lessless at line 26 col 15 changed to labelI_
\* Procedure variable labelJ of procedure lessless at line 26 col 23 changed to labelJ_
\* Parameter i of procedure lessless at line 25 col 20 changed to i_l
\* Parameter j of procedure lessless at line 25 col 23 changed to j_l
CONSTANT defaultInitValue
VARIABLES choosing, label, lessLessProcResult, maxProcResult, pc, stack, 
          isEndless, i_l, j_l, labelI_, labelJ_, m, k, temp, i, j, labelI, 
          labelJ, i_, j_, otherprocesses

vars == << choosing, label, lessLessProcResult, maxProcResult, pc, stack, 
           isEndless, i_l, j_l, labelI_, labelJ_, m, k, temp, i, j, labelI, 
           labelJ, i_, j_, otherprocesses >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ choosing = [x \in 1..N |-> FALSE]
        /\ label = [x \in 1..N |-> 0]
        /\ lessLessProcResult = [x \in 1..N |-> FALSE]
        /\ maxProcResult = [x \in 1..N |-> 0]
        (* Procedure NonCriticalSection *)
        /\ isEndless = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure lessless *)
        /\ i_l = [ self \in ProcSet |-> defaultInitValue]
        /\ j_l = [ self \in ProcSet |-> defaultInitValue]
        /\ labelI_ = [ self \in ProcSet |-> defaultInitValue]
        /\ labelJ_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure max *)
        /\ m = [ self \in ProcSet |-> -1]
        /\ k = [ self \in ProcSet |-> 1]
        /\ temp = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure wait *)
        /\ i = [ self \in ProcSet |-> defaultInitValue]
        /\ j = [ self \in ProcSet |-> defaultInitValue]
        /\ labelI = [ self \in ProcSet |-> defaultInitValue]
        /\ labelJ = [ self \in ProcSet |-> defaultInitValue]
        (* Process Proc *)
        /\ i_ = [self \in 1..N |-> self]
        /\ j_ = [self \in 1..N |-> defaultInitValue]
        /\ otherprocesses = [self \in 1..N |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "p0"]

nonCritical0(self) == /\ pc[self] = "nonCritical0"
                      /\ \E x \in {0,1}:
                           isEndless' = [isEndless EXCEPT ![self] = x]
                      /\ pc' = [pc EXCEPT ![self] = "nonCritical1"]
                      /\ UNCHANGED << choosing, label, lessLessProcResult, 
                                      maxProcResult, stack, i_l, j_l, labelI_, 
                                      labelJ_, m, k, temp, i, j, labelI, 
                                      labelJ, i_, j_, otherprocesses >>

nonCritical1(self) == /\ pc[self] = "nonCritical1"
                      /\ IF (isEndless[self] = 1)
                            THEN /\ pc' = [pc EXCEPT ![self] = "nonCritical2"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "nonCritical4"]
                      /\ UNCHANGED << choosing, label, lessLessProcResult, 
                                      maxProcResult, stack, isEndless, i_l, 
                                      j_l, labelI_, labelJ_, m, k, temp, i, j, 
                                      labelI, labelJ, i_, j_, otherprocesses >>

nonCritical2(self) == /\ pc[self] = "nonCritical2"
                      /\ pc' = [pc EXCEPT ![self] = "nonCritical3"]
                      /\ UNCHANGED << choosing, label, lessLessProcResult, 
                                      maxProcResult, stack, isEndless, i_l, 
                                      j_l, labelI_, labelJ_, m, k, temp, i, j, 
                                      labelI, labelJ, i_, j_, otherprocesses >>

nonCritical3(self) == /\ pc[self] = "nonCritical3"
                      /\ TRUE
                      /\ pc' = [pc EXCEPT ![self] = "nonCritical2"]
                      /\ UNCHANGED << choosing, label, lessLessProcResult, 
                                      maxProcResult, stack, isEndless, i_l, 
                                      j_l, labelI_, labelJ_, m, k, temp, i, j, 
                                      labelI, labelJ, i_, j_, otherprocesses >>

nonCritical4(self) == /\ pc[self] = "nonCritical4"
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ isEndless' = [isEndless EXCEPT ![self] = Head(stack[self]).isEndless]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << choosing, label, lessLessProcResult, 
                                      maxProcResult, i_l, j_l, labelI_, 
                                      labelJ_, m, k, temp, i, j, labelI, 
                                      labelJ, i_, j_, otherprocesses >>

NonCriticalSection(self) == nonCritical0(self) \/ nonCritical1(self)
                               \/ nonCritical2(self) \/ nonCritical3(self)
                               \/ nonCritical4(self)

ll1(self) == /\ pc[self] = "ll1"
             /\ labelI_' = [labelI_ EXCEPT ![self] = label[i_l[self]]]
             /\ pc' = [pc EXCEPT ![self] = "ll2"]
             /\ UNCHANGED << choosing, label, lessLessProcResult, 
                             maxProcResult, stack, isEndless, i_l, j_l, 
                             labelJ_, m, k, temp, i, j, labelI, labelJ, i_, j_, 
                             otherprocesses >>

ll2(self) == /\ pc[self] = "ll2"
             /\ labelJ_' = [labelJ_ EXCEPT ![self] = label[j_l[self]]]
             /\ pc' = [pc EXCEPT ![self] = "ll3"]
             /\ UNCHANGED << choosing, label, lessLessProcResult, 
                             maxProcResult, stack, isEndless, i_l, j_l, 
                             labelI_, m, k, temp, i, j, labelI, labelJ, i_, j_, 
                             otherprocesses >>

ll3(self) == /\ pc[self] = "ll3"
             /\ IF (labelI_[self] < labelJ_[self])
                   THEN /\ lessLessProcResult' = [lessLessProcResult EXCEPT ![i_l[self]] = TRUE]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ labelI_' = [labelI_ EXCEPT ![self] = Head(stack[self]).labelI_]
                        /\ labelJ_' = [labelJ_ EXCEPT ![self] = Head(stack[self]).labelJ_]
                        /\ i_l' = [i_l EXCEPT ![self] = Head(stack[self]).i_l]
                        /\ j_l' = [j_l EXCEPT ![self] = Head(stack[self]).j_l]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "ll4"]
                        /\ UNCHANGED << lessLessProcResult, stack, i_l, j_l, 
                                        labelI_, labelJ_ >>
             /\ UNCHANGED << choosing, label, maxProcResult, isEndless, m, k, 
                             temp, i, j, labelI, labelJ, i_, j_, 
                             otherprocesses >>

ll4(self) == /\ pc[self] = "ll4"
             /\ IF (labelI_[self] = labelJ_[self] /\ i_l[self] < j_l[self])
                   THEN /\ lessLessProcResult' = [lessLessProcResult EXCEPT ![i_l[self]] = TRUE]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ labelI_' = [labelI_ EXCEPT ![self] = Head(stack[self]).labelI_]
                        /\ labelJ_' = [labelJ_ EXCEPT ![self] = Head(stack[self]).labelJ_]
                        /\ i_l' = [i_l EXCEPT ![self] = Head(stack[self]).i_l]
                        /\ j_l' = [j_l EXCEPT ![self] = Head(stack[self]).j_l]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "ll5"]
                        /\ UNCHANGED << lessLessProcResult, stack, i_l, j_l, 
                                        labelI_, labelJ_ >>
             /\ UNCHANGED << choosing, label, maxProcResult, isEndless, m, k, 
                             temp, i, j, labelI, labelJ, i_, j_, 
                             otherprocesses >>

ll5(self) == /\ pc[self] = "ll5"
             /\ lessLessProcResult' = [lessLessProcResult EXCEPT ![i_l[self]] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ labelI_' = [labelI_ EXCEPT ![self] = Head(stack[self]).labelI_]
             /\ labelJ_' = [labelJ_ EXCEPT ![self] = Head(stack[self]).labelJ_]
             /\ i_l' = [i_l EXCEPT ![self] = Head(stack[self]).i_l]
             /\ j_l' = [j_l EXCEPT ![self] = Head(stack[self]).j_l]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << choosing, label, maxProcResult, isEndless, m, k, 
                             temp, i, j, labelI, labelJ, i_, j_, 
                             otherprocesses >>

lessless(self) == ll1(self) \/ ll2(self) \/ ll3(self) \/ ll4(self)
                     \/ ll5(self)

max1(self) == /\ pc[self] = "max1"
              /\ IF (k[self] <= N)
                    THEN /\ pc' = [pc EXCEPT ![self] = "max2"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "max4"]
              /\ UNCHANGED << choosing, label, lessLessProcResult, 
                              maxProcResult, stack, isEndless, i_l, j_l, 
                              labelI_, labelJ_, m, k, temp, i, j, labelI, 
                              labelJ, i_, j_, otherprocesses >>

max2(self) == /\ pc[self] = "max2"
              /\ temp' = [temp EXCEPT ![self] = label[k[self]]]
              /\ pc' = [pc EXCEPT ![self] = "max3"]
              /\ UNCHANGED << choosing, label, lessLessProcResult, 
                              maxProcResult, stack, isEndless, i_l, j_l, 
                              labelI_, labelJ_, m, k, i, j, labelI, labelJ, i_, 
                              j_, otherprocesses >>

max3(self) == /\ pc[self] = "max3"
              /\ IF (temp[self] > m[self])
                    THEN /\ m' = [m EXCEPT ![self] = temp[self]]
                    ELSE /\ TRUE
                         /\ m' = m
              /\ k' = [k EXCEPT ![self] = k[self]+1]
              /\ pc' = [pc EXCEPT ![self] = "max1"]
              /\ UNCHANGED << choosing, label, lessLessProcResult, 
                              maxProcResult, stack, isEndless, i_l, j_l, 
                              labelI_, labelJ_, temp, i, j, labelI, labelJ, i_, 
                              j_, otherprocesses >>

max4(self) == /\ pc[self] = "max4"
              /\ maxProcResult' = [maxProcResult EXCEPT ![self] = m[self]]
              /\ pc' = [pc EXCEPT ![self] = "max5"]
              /\ UNCHANGED << choosing, label, lessLessProcResult, stack, 
                              isEndless, i_l, j_l, labelI_, labelJ_, m, k, 
                              temp, i, j, labelI, labelJ, i_, j_, 
                              otherprocesses >>

max5(self) == /\ pc[self] = "max5"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ m' = [m EXCEPT ![self] = Head(stack[self]).m]
              /\ k' = [k EXCEPT ![self] = Head(stack[self]).k]
              /\ temp' = [temp EXCEPT ![self] = Head(stack[self]).temp]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << choosing, label, lessLessProcResult, 
                              maxProcResult, isEndless, i_l, j_l, labelI_, 
                              labelJ_, i, j, labelI, labelJ, i_, j_, 
                              otherprocesses >>

max(self) == max1(self) \/ max2(self) \/ max3(self) \/ max4(self)
                \/ max5(self)

wait1(self) == /\ pc[self] = "wait1"
               /\ pc' = [pc EXCEPT ![self] = "wait2"]
               /\ UNCHANGED << choosing, label, lessLessProcResult, 
                               maxProcResult, stack, isEndless, i_l, j_l, 
                               labelI_, labelJ_, m, k, temp, i, j, labelI, 
                               labelJ, i_, j_, otherprocesses >>

wait2(self) == /\ pc[self] = "wait2"
               /\ labelI' = [labelI EXCEPT ![self] = label[i[self]]]
               /\ pc' = [pc EXCEPT ![self] = "wait3"]
               /\ UNCHANGED << choosing, label, lessLessProcResult, 
                               maxProcResult, stack, isEndless, i_l, j_l, 
                               labelI_, labelJ_, m, k, temp, i, j, labelJ, i_, 
                               j_, otherprocesses >>

wait3(self) == /\ pc[self] = "wait3"
               /\ labelJ' = [labelJ EXCEPT ![self] = label[j[self]]]
               /\ pc' = [pc EXCEPT ![self] = "wait4"]
               /\ UNCHANGED << choosing, label, lessLessProcResult, 
                               maxProcResult, stack, isEndless, i_l, j_l, 
                               labelI_, labelJ_, m, k, temp, i, j, labelI, i_, 
                               j_, otherprocesses >>

wait4(self) == /\ pc[self] = "wait4"
               /\ /\ i_l' = [i_l EXCEPT ![self] = i[self]]
                  /\ j_l' = [j_l EXCEPT ![self] = j[self]]
                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lessless",
                                                           pc        |->  "wait5",
                                                           labelI_   |->  labelI_[self],
                                                           labelJ_   |->  labelJ_[self],
                                                           i_l       |->  i_l[self],
                                                           j_l       |->  j_l[self] ] >>
                                                       \o stack[self]]
               /\ labelI_' = [labelI_ EXCEPT ![self] = defaultInitValue]
               /\ labelJ_' = [labelJ_ EXCEPT ![self] = defaultInitValue]
               /\ pc' = [pc EXCEPT ![self] = "ll1"]
               /\ UNCHANGED << choosing, label, lessLessProcResult, 
                               maxProcResult, isEndless, m, k, temp, i, j, 
                               labelI, labelJ, i_, j_, otherprocesses >>

wait5(self) == /\ pc[self] = "wait5"
               /\ IF (labelJ[self] = 0 \/ lessLessProcResult[i[self]] = TRUE)
                     THEN /\ pc' = [pc EXCEPT ![self] = "wait6"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "wait1"]
               /\ UNCHANGED << choosing, label, lessLessProcResult, 
                               maxProcResult, stack, isEndless, i_l, j_l, 
                               labelI_, labelJ_, m, k, temp, i, j, labelI, 
                               labelJ, i_, j_, otherprocesses >>

wait6(self) == /\ pc[self] = "wait6"
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ labelI' = [labelI EXCEPT ![self] = Head(stack[self]).labelI]
               /\ labelJ' = [labelJ EXCEPT ![self] = Head(stack[self]).labelJ]
               /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
               /\ j' = [j EXCEPT ![self] = Head(stack[self]).j]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << choosing, label, lessLessProcResult, 
                               maxProcResult, isEndless, i_l, j_l, labelI_, 
                               labelJ_, m, k, temp, i_, j_, otherprocesses >>

wait(self) == wait1(self) \/ wait2(self) \/ wait3(self) \/ wait4(self)
                 \/ wait5(self) \/ wait6(self)

p0(self) == /\ pc[self] = "p0"
            /\ pc' = [pc EXCEPT ![self] = "p1"]
            /\ UNCHANGED << choosing, label, lessLessProcResult, maxProcResult, 
                            stack, isEndless, i_l, j_l, labelI_, labelJ_, m, k, 
                            temp, i, j, labelI, labelJ, i_, j_, otherprocesses >>

p1(self) == /\ pc[self] = "p1"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "NonCriticalSection",
                                                     pc        |->  "p2",
                                                     isEndless |->  isEndless[self] ] >>
                                                 \o stack[self]]
            /\ isEndless' = [isEndless EXCEPT ![self] = defaultInitValue]
            /\ pc' = [pc EXCEPT ![self] = "nonCritical0"]
            /\ UNCHANGED << choosing, label, lessLessProcResult, maxProcResult, 
                            i_l, j_l, labelI_, labelJ_, m, k, temp, i, j, 
                            labelI, labelJ, i_, j_, otherprocesses >>

p2(self) == /\ pc[self] = "p2"
            /\ choosing' = [choosing EXCEPT ![i_[self]] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "p3a"]
            /\ UNCHANGED << label, lessLessProcResult, maxProcResult, stack, 
                            isEndless, i_l, j_l, labelI_, labelJ_, m, k, temp, 
                            i, j, labelI, labelJ, i_, j_, otherprocesses >>

p3a(self) == /\ pc[self] = "p3a"
             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "max",
                                                      pc        |->  "p3b",
                                                      m         |->  m[self],
                                                      k         |->  k[self],
                                                      temp      |->  temp[self] ] >>
                                                  \o stack[self]]
             /\ m' = [m EXCEPT ![self] = -1]
             /\ k' = [k EXCEPT ![self] = 1]
             /\ temp' = [temp EXCEPT ![self] = defaultInitValue]
             /\ pc' = [pc EXCEPT ![self] = "max1"]
             /\ UNCHANGED << choosing, label, lessLessProcResult, 
                             maxProcResult, isEndless, i_l, j_l, labelI_, 
                             labelJ_, i, j, labelI, labelJ, i_, j_, 
                             otherprocesses >>

p3b(self) == /\ pc[self] = "p3b"
             /\ IF (maxProcResult[self] >= MaxTokenNumber)
                   THEN /\ maxProcResult' = [maxProcResult EXCEPT ![self] = MaxTokenNumber-1]
                   ELSE /\ TRUE
                        /\ UNCHANGED maxProcResult
             /\ pc' = [pc EXCEPT ![self] = "p3c"]
             /\ UNCHANGED << choosing, label, lessLessProcResult, stack, 
                             isEndless, i_l, j_l, labelI_, labelJ_, m, k, temp, 
                             i, j, labelI, labelJ, i_, j_, otherprocesses >>

p3c(self) == /\ pc[self] = "p3c"
             /\ label' = [label EXCEPT ![i_[self]] = 1 + maxProcResult[self]]
             /\ pc' = [pc EXCEPT ![self] = "p4"]
             /\ UNCHANGED << choosing, lessLessProcResult, maxProcResult, 
                             stack, isEndless, i_l, j_l, labelI_, labelJ_, m, 
                             k, temp, i, j, labelI, labelJ, i_, j_, 
                             otherprocesses >>

p4(self) == /\ pc[self] = "p4"
            /\ choosing' = [choosing EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "p5a"]
            /\ UNCHANGED << label, lessLessProcResult, maxProcResult, stack, 
                            isEndless, i_l, j_l, labelI_, labelJ_, m, k, temp, 
                            i, j, labelI, labelJ, i_, j_, otherprocesses >>

p5a(self) == /\ pc[self] = "p5a"
             /\ otherprocesses' = [otherprocesses EXCEPT ![self] = 1..N \ {i_[self]}]
             /\ pc' = [pc EXCEPT ![self] = "p5b"]
             /\ UNCHANGED << choosing, label, lessLessProcResult, 
                             maxProcResult, stack, isEndless, i_l, j_l, 
                             labelI_, labelJ_, m, k, temp, i, j, labelI, 
                             labelJ, i_, j_ >>

p5b(self) == /\ pc[self] = "p5b"
             /\ IF (otherprocesses[self] # {})
                   THEN /\ \E proc \in otherprocesses[self]:
                             j_' = [j_ EXCEPT ![self] = proc]
                        /\ otherprocesses' = [otherprocesses EXCEPT ![self] = otherprocesses[self] \ {j_'[self]}]
                        /\ pc' = [pc EXCEPT ![self] = "p6"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "criticalSection"]
                        /\ UNCHANGED << j_, otherprocesses >>
             /\ UNCHANGED << choosing, label, lessLessProcResult, 
                             maxProcResult, stack, isEndless, i_l, j_l, 
                             labelI_, labelJ_, m, k, temp, i, j, labelI, 
                             labelJ, i_ >>

p6(self) == /\ pc[self] = "p6"
            /\ choosing[j_[self]] = FALSE
            /\ pc' = [pc EXCEPT ![self] = "p7"]
            /\ UNCHANGED << choosing, label, lessLessProcResult, maxProcResult, 
                            stack, isEndless, i_l, j_l, labelI_, labelJ_, m, k, 
                            temp, i, j, labelI, labelJ, i_, j_, otherprocesses >>

p7(self) == /\ pc[self] = "p7"
            /\ /\ i' = [i EXCEPT ![self] = i_[self]]
               /\ j' = [j EXCEPT ![self] = j_[self]]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wait",
                                                        pc        |->  "p5b",
                                                        labelI    |->  labelI[self],
                                                        labelJ    |->  labelJ[self],
                                                        i         |->  i[self],
                                                        j         |->  j[self] ] >>
                                                    \o stack[self]]
            /\ labelI' = [labelI EXCEPT ![self] = defaultInitValue]
            /\ labelJ' = [labelJ EXCEPT ![self] = defaultInitValue]
            /\ pc' = [pc EXCEPT ![self] = "wait1"]
            /\ UNCHANGED << choosing, label, lessLessProcResult, maxProcResult, 
                            isEndless, i_l, j_l, labelI_, labelJ_, m, k, temp, 
                            i_, j_, otherprocesses >>

criticalSection(self) == /\ pc[self] = "criticalSection"
                         /\ TRUE
                         /\ pc' = [pc EXCEPT ![self] = "p9"]
                         /\ UNCHANGED << choosing, label, lessLessProcResult, 
                                         maxProcResult, stack, isEndless, i_l, 
                                         j_l, labelI_, labelJ_, m, k, temp, i, 
                                         j, labelI, labelJ, i_, j_, 
                                         otherprocesses >>

p9(self) == /\ pc[self] = "p9"
            /\ label' = [label EXCEPT ![i_[self]] = 0]
            /\ pc' = [pc EXCEPT ![self] = "p0"]
            /\ UNCHANGED << choosing, lessLessProcResult, maxProcResult, stack, 
                            isEndless, i_l, j_l, labelI_, labelJ_, m, k, temp, 
                            i, j, labelI, labelJ, i_, j_, otherprocesses >>

Proc(self) == p0(self) \/ p1(self) \/ p2(self) \/ p3a(self) \/ p3b(self)
                 \/ p3c(self) \/ p4(self) \/ p5a(self) \/ p5b(self)
                 \/ p6(self) \/ p7(self) \/ criticalSection(self)
                 \/ p9(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ NonCriticalSection(self) \/ lessless(self)
                               \/ max(self) \/ wait(self))
           \/ (\E self \in 1..N: Proc(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-a305d95659eee014241349ed81fc975a
CriticalSectionInvariant == \A proc1, proc2 \in 1..N : (proc1 # proc2) => ~ (pc[proc1] = "criticalSection" /\ pc[proc2] = "criticalSection")
MaxTokenInvariant == \A proc1 \in 1..N : maxProcResult[proc1] <= MaxTokenNumber - 1
CheckOrderCorrectnes(s) == ~\E t \in 1..N : 
                            /\ label[t] > 0 
                            /\ label[t] <= label[s] 
                            /\ t < s
                            /\ pc[t] \in {"p7"} \/ pc[t] \in {"p6"}
CriticalSectionOrderInvariant == \A s \in 1..N:
                                    /\ pc[s] \in {"criticalSection"}
                                    => CheckOrderCorrectnes(s) 
=============================================================================
\* Modification History
\* Last modified Thu Jan 07 12:54:56 MSK 2021 by a18535673
\* Created Tue Jan 05 21:07:12 MSK 2021 by a18535673

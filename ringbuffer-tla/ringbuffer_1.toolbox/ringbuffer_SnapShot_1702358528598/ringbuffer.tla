----------------------------- MODULE ringbuffer -----------------------------



\* Modification History
\* Last modified Tue Dec 12 05:21:58 GMT 2023 by samue
\* Created Sat Dec 09 14:08:07 GMT 2023 by samue

EXTENDS Integers, TLC

CONSTANTS
    \* Number of philosophers
    NThreads,
    assigned
    
VARIABLES sent, threads, pc

vars == << sent, threads, pc >>

ASSUME
    /\ NThreads \in Nat \ {0}

\* Choose something to represent the absence of a value. *.



ASSUME
    /\ NThreads \in Nat \ {0}

(* --algorithm RingBuffer

variables

sent = {}
types = {"reader", "writer"}

 threads = [
        thread \in 1..NThreads |-> [
    \* We create a thread proportion according to the assigned list
            type |-> assigned[thread],
            start |-> 0,
            endr |-> 0
            full |-> FALSE
        ]
      ]

    
fair process Thread \in 1..NThreads
\* This acts like a member variable and you can access it like one. But we're
\* actually creating an array with one element per process, and the "member
\* variable" we access is just the corresponding bucket in that array.

            
begin
WriterCheck:
    while TRUE do
        if threads[Thread].type = "writer" then
            otherThread \in 1..Nthreads
                if threads[Thread].endr + 1 = threads[otherThread].start then
                    threads[Thread].full := TRUE
                end if;
                    
               
        end if;

WriterWrite:
    if threads[Thread].full == FALSE then
        Append(sent, [
            Reader |-> "not-read",
            Writer |-> "written"
        ])
    endr := end + 1
    PrintT(endr)
    end if;
        
      
ReaderCheck:

    if threads[Thread].type = "reader" then
          
        if threads[Thread].start = threads[0].endr then
            threads[Thread].empty := TRUE
        end if;
        if threads[Thread].empty = FALSE then
            threads[Thread].start := threads[Thread].start + 1
            sent[threads[0].endr].Reader := "read"
            threads[Thread].start := threads[Thread].start + 1
            PrintT(threads[Thread].start)
        end if
    end if;

    end while;
    
end process;
        
end algorithm; *)



ProcSet == (1..NThreads)





               
    
Init == (* Global variables *)
    /\ threads = [
        thread \in 1..NThreads |-> [
    \* We create a thread proportion according to the assigned list
            type |-> assigned[thread],
            start |-> 0,
            endr |-> 0
        ]
      ]
   /\ sent = [
            Reader |-> "not-read",
            Writer |-> "written"
        ]
   /\ pc = [self \in ProcSet |-> IF assigned[self] = "writer" THEN "WriterCheck" ELSE "ReaderCheck"]


\*Loop(self) == /\ pc[self] = "Loop"
\*              /\ IF /\ forks[LeftFork(self)].holder = self
\*                    /\ ~forks[LeftFork(self)].clean
\*                    THEN /\ forks' = [forks EXCEPT ![LeftFork(self)] =                          [
\*                                                                           holder |-> LeftPhilosopher(self),
\*                                                                           clean |-> TRUE
\*                                                                       ]]
\*                    ELSE /\ IF /\ forks[RightFork(self)].holder = self
\*                               /\ ~forks[RightFork(self)].clean
\*                               THEN /\ forks' = [forks EXCEPT ![RightFork(self)] =                           [
\*                                                                                       holder |-> RightPhilosopher(self),
\*                                                                                       clean |-> TRUE
\*                                                                                   ]]
\*                               ELSE /\ TRUE
\*                                    /\ forks' = forks
\*              /\ IF hungry[self]
\*                    THEN /\ IF CanEat(self)
\*                               THEN /\ pc' = [pc EXCEPT ![self] = "Eat"]
\*                               ELSE /\ pc' = [pc EXCEPT ![self] = "Loop"]
\*                    ELSE /\ pc' = [pc EXCEPT ![self] = "Think"]
\*              /\ UNCHANGED hungry

Check(self) == /\ IF threads[self].type = "writer"
                   THEN /\ pc[self] = "WriterCheck"
                        /\ threads' = threads
                        /\ sent' = sent
                        /\ pc' = pc
                        
                   ELSE /\ IF threads[self].type = "reader"
                           THEN /\ pc[self] = "ReaderCheck"
                                /\ threads' = threads
                                /\ sent' = sent
                                /\ pc' = pc
                           ELSE /\ threads' = threads
                                /\ sent' = sent
                                /\ pc' = pc
                



Thread(self) == Check(self)
                   
                      
Next == (\E self \in 1..NThreads: Thread(self))       

----





Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..NThreads : WF_vars(Thread(self))
        
EndAboveStart == \A thread \in 1..NThreads:
                       /\ threads[thread].endr >= threads[thread].start
AllRead ==
   \A item \in sent:
        /\ item.Reader = "read"         
====
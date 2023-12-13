----------------------------- MODULE ringbuffer -----------------------------



\* Modification History
\* Last modified Wed Dec 13 17:23:57 GMT 2023 by samue
\* Created Sat Dec 09 14:08:07 GMT 2023 by samue

EXTENDS Integers, TLC, Sequences

CONSTANTS
    \* Number of philosophers
    NThreads,
    assigned,
    size
    
VARIABLES sent, threads, pc, counter, step


vars == << sent, threads, pc, counter, step >>

ASSUME
    /\ NThreads \in Nat \ {0}

\* Choose something to represent the absence of a value. *.



ASSUME
    /\ NThreads \in Nat \ {0}

(* --algorithm RingBuffer

variables threads

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
        PrintT(threads[Thread].start)
        PrintT(threads[Thread].endr)
        
        if threads[Thread].type = "writer" then
            threads[1].full := FALSE
            otherThread \in 1..NThreads
                if (threads[1].endr + 1) % size = threads[otherThread].start then
                    threads[1].full := TRUE
                end if;
                    
               
        

WriterWrite:
        if threads[1].full == FALSE then
           sent[(threads[1].endr + 1) % size] = [
                Reader |-> "not-read",
                Writer |-> "written"
            ])
            endr := 1 + ((threads[1].endr + 1) % size)
            PrintT(threads[1].endr)
        end if;
    end if;
      
ReaderCheck:

    if threads[Thread].type = "reader" then
        threads[Thread].empty := FALSE  
        if threads[Thread].start = threads[1].endr then
            threads[Thread].empty := TRUE
        end if;
        if threads[Thread].empty = FALSE then
            sent[threads[Thread].start].Reader := "read"
            threads[Thread].start := 1 + (threads[Thread].start + 1) % size
           
            
            
        end if
    end if;

    end while;
    
end process;
        
end algorithm; *)



ProcSet == (1..NThreads)





               
    
Init == (* Global variables *)
    /\ counter = "init"
    /\ step = 0
    /\ sent = [
        thread \in 1..size |-> [
               Writer |-> "not-written",
               Reader |-> "not-read"
        ]
      ]
    /\ threads = [
        thread \in 1..NThreads |-> [
    \* We create a thread proportion according to the assigned list
            type |-> assigned[thread],
            start |-> 1,
            endr |-> 1
        ]
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



Full(self) == \A thread \in 2..NThreads:
                    \/ threads[thread].start = (1 + ((threads[1].endr + 1) % size))

Empty(self) == threads[self].start = threads[1].endr

\*/\ IF ~(Len(sent) = size) THEN
\*                    /\ threads' = threads
\*                    /\ sent' = sent
\*                    /\ pc' = pc
\*                    /\ counter' = "finished"
\*                    /\ step' = step
\*                 ELSE 

ThreadWorker(self) == \/ \E thread \in 2..NThreads:
                        IF ~Empty(thread)
                        THEN
                            /\ threads' = [threads EXCEPT ![thread] = [
                                start |-> 1 + ((threads[thread].start + 1) % size),
                                type |-> (threads[thread].type),
                                endr |-> (threads[thread].endr) 
                               ]]
                            /\ sent' = [sent EXCEPT ![threads[thread].start].Reader = "read"]
                            /\ pc' = pc
                            /\ step' = step
                            /\ counter = "read"
                        ELSE (* Do nothing *)
                            /\ threads' = threads
                            /\ sent' = sent
                            /\ pc' = pc
                            /\ counter' = "empty-cannot-read"
                            /\ step' = step
                   \/ IF ~Full(self)
                       THEN 
                           (* [s EXCEPT ![1] = FALSE] *)
                            /\ threads' = [threads EXCEPT ![1] = [
                                endr |-> 1 + ((threads[1].endr + 1) % size),
                                type |-> (threads[1].type),
                                start |-> (threads[1].start)
                               ]]
                            /\ sent' = [sent EXCEPT ![threads[1].endr] = [
                                Writer |-> "written",
                                Reader |-> "not-read"
                               ]]
                            /\ pc' = pc
                            /\ counter' = "written-step"
                            /\ step' = step
                       ELSE (* Do nothing *)
                        /\ threads' = threads
                        /\ sent' = sent
                        /\ pc' = pc
                        /\ counter' = "full-cannot-write"
                        /\ step' = step
                    
           

                 
                      
Next == (\E self \in 1..NThreads: ThreadWorker(self))
----





Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in 2..NThreads : WF_vars(ThreadWorker(self))
        
EndAboveStart == \A thread \in 1..NThreads:
                       /\ threads[1].endr >= threads[thread].start
AllRead ==
   \E item \in sent:
        /\ item.Reader = "read"         
====
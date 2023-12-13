----------------------------- MODULE ringbuffer -----------------------------



\* Modification History
\* Last modified Wed Dec 13 14:44:12 GMT 2023 by samue
\* Created Sat Dec 09 14:08:07 GMT 2023 by samue

EXTENDS Integers, TLC, Sequences

CONSTANTS
    \* Number of philosophers
    NThreads,
    assigned,
    size
    
VARIABLES sent, threads, pc, counter


vars == << sent, threads, pc, counter >>

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
        threads[1].full := FALSE
        if threads[Thread].type = "writer" then
            otherThread \in 1..NThreads
                if (threads[1].endr + 1) % size = threads[otherThread].start then
                    threads[1].full := TRUE
                end if;
                    
               
        end if;

WriterWrite:
    if threads[Thread].full == FALSE then
        Append(sent, [
            Reader |-> "not-read",
            Writer |-> "written"
        ])
        endr := (threads[1].endr + 1) % size
        PrintT(threads[1].endr)
    end if;
        
      
ReaderCheck:

    if threads[Thread].type = "reader" then
        threads[Thread].empty := FALSE  
        if threads[Thread].start = threads[1].endr then
            threads[Thread].empty := TRUE
        end if;
        if threads[Thread].empty = FALSE then
            sent[threads[Thread].start].Reader := "read"
            threads[Thread].start := (threads[Thread].start + 1) % size
           
            
            
        end if
    end if;

    end while;
    
end process;
        
end algorithm; *)



ProcSet == (1..NThreads)





               
    
Init == (* Global variables *)
    /\ counter = 0
    /\ threads = [
        thread \in 1..NThreads |-> [
    \* We create a thread proportion according to the assigned list
            type |-> assigned[thread],
            start |-> 0,
            endr |-> 0
        ]
      ]
   /\ sent = <<>>
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
                    /\ threads[thread].start = (threads[1].endr + 1) % size

Empty(self) == /\ threads[self].start = threads[1].endr

Check(self) == /\ IF threads[self].type = "writer"
                   THEN /\ IF ~Full(self)
                           THEN /\ threads[1] = [
                                    endr |-> (threads[1].endr + 1) % size 
                                   ]
                                /\ sent' = Append(sent, [
                                    Writer |-> "written",
                                    Reader |-> "not-read"
                                   ])
                                /\ pc' = pc
                                /\ counter = counter + 1
                           ELSE (* Do nothing *)
                            /\ threads' = threads
                            /\ sent' = sent
                            /\ pc' = pc
                            /\ counter = counter + 1
                        
                  ELSE IF threads[self].type = "reader"
                       THEN IF ~Empty(self)
                            THEN 
                                /\ PrintT(threads[self].start)
                                /\ threads[self]' = [
                                    start |-> (threads[1].start + 1) % size 
                                   ]
                                /\ sent[threads[self].start]' = [
                                        Writer |-> "read"
                                   ]
                                /\ pc' = pc
                            ELSE (* Do nothing *)
                            /\ threads' = threads
                            /\ sent' = sent
                            /\ pc' = pc
                            /\ counter = counter + 1
                       ELSE (* Do nothing *)
                            /\ threads' = threads
                            /\ sent' = sent
                            /\ pc' = pc
                            /\ counter = counter + 1
                



Thread(self) == /\ Check(self)
                   
                      
Next == (\A self \in 1..NThreads: Thread(self))       

----





Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..NThreads : WF_vars(Thread(self))
        
EndAboveStart == \A thread \in 1..NThreads:
                       /\ threads[thread].endr >= threads[thread].start
AllRead ==
   \A item \in sent:
        /\ item.Reader = "read"         
====
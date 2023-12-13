---- MODULE MC_TTrace_1702483462 ----
EXTENDS Sequences, TLCExt, MC, Toolbox, Naturals, TLC

_expression ==
    LET MC_TEExpression == INSTANCE MC_TEExpression
    IN MC_TEExpression!expression
----

_trace ==
    LET MC_TETrace == INSTANCE MC_TETrace
    IN MC_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        pc = (<<"WriterCheck", "ReaderCheck", "ReaderCheck">>)
        /\
        threads = (<<[endr |-> 1], [type |-> "reader", start |-> 0, endr |-> 0], [type |-> "reader", start |-> 0, endr |-> 0]>>)
        /\
        step = (0)
        /\
        counter = ("written-step")
        /\
        sent = (<<>>)
    )
----

_init ==
    /\ counter = _TETrace[1].counter
    /\ threads = _TETrace[1].threads
    /\ step = _TETrace[1].step
    /\ sent = _TETrace[1].sent
    /\ pc = _TETrace[1].pc
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ counter  = _TETrace[i].counter
        /\ counter' = _TETrace[j].counter
        /\ threads  = _TETrace[i].threads
        /\ threads' = _TETrace[j].threads
        /\ step  = _TETrace[i].step
        /\ step' = _TETrace[j].step
        /\ sent  = _TETrace[i].sent
        /\ sent' = _TETrace[j].sent
        /\ pc  = _TETrace[i].pc
        /\ pc' = _TETrace[j].pc

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("MC_TTrace_1702483462.json", _TETrace)

=============================================================================

 Note that you can extract this module `MC_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `MC_TEExpression.tla` file takes precedence 
  over the module `MC_TEExpression` below).

---- MODULE MC_TEExpression ----
EXTENDS Sequences, TLCExt, MC, Toolbox, Naturals, TLC

expression == 
    [
        \* To hide variables of the `MC` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        counter |-> counter
        ,threads |-> threads
        ,step |-> step
        ,sent |-> sent
        ,pc |-> pc
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_counterUnchanged |-> counter = counter'
        
        \* Format the `counter` variable as Json value.
        \* ,_counterJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(counter)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_counterModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].counter # _TETrace[s-1].counter
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE MC_TETrace ----
\*EXTENDS IOUtils, MC, TLC
\*
\*trace == IODeserialize("MC_TTrace_1702483462.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE MC_TETrace ----
EXTENDS MC, TLC

trace == 
    <<
    ([pc |-> <<"WriterCheck", "ReaderCheck", "ReaderCheck">>,threads |-> <<[type |-> "writer", start |-> 0, endr |-> 0], [type |-> "reader", start |-> 0, endr |-> 0], [type |-> "reader", start |-> 0, endr |-> 0]>>,step |-> 0,counter |-> "init",sent |-> <<>>]),
    ([pc |-> <<"WriterCheck", "ReaderCheck", "ReaderCheck">>,threads |-> <<[endr |-> 1], [type |-> "reader", start |-> 0, endr |-> 0], [type |-> "reader", start |-> 0, endr |-> 0]>>,step |-> 0,counter |-> "written-step",sent |-> <<>>])
    >>
----


=============================================================================

---- CONFIG MC_TTrace_1702483462 ----
CONSTANTS
    NThreads <- const_1702483445747197000
    assigned <- const_1702483445747198000
    size <- const_1702483445747199000

INVARIANT
    _inv

CHECK_DEADLOCK
    \* CHECK_DEADLOCK off because of PROPERTY or INVARIANT above.
    FALSE

INIT
    _init

NEXT
    _next

CONSTANT
    _TETrace <- _trace

ALIAS
    _expression
=============================================================================
\* Generated on Wed Dec 13 16:04:24 GMT 2023
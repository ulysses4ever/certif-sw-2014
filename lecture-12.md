# Verification of cryprographic protocols

It's a traditional application for proof assistants. It dates back to 90-s,
when this work was done in Isabelle HOL assistant. We translate this, namely
Needham-Shroeder protocol analysis, to Coq.

In cryptography setting we usually have number of **agents**, who perform some
actions. We usually call them _Alice_, _Bob_, etc. We also usually have 
**messages**. We gonna dive in asymmetric cryptography, which implies that we
will have public keys _K<sub>A</sub>_ and secret keys _SK<sub>A</sub>_. We will
denote messages encrypted with _K<sub>A</sub>_ as: {_m_}<sub>_K<sub>A</sub>_</sub>.
THe setting is as following: anyone knows public key _K<sub>A</sub>_ and can
_encrypt_ any message, but ony _A_ knows secret key _SK<sub>A</sub>_ and can 
_decrypt_ cryptogramms.

We have usuall tasks in public key cryptography:

1. Key exchange.
2. Authentification.

Let's discuss a protocol for authentification. We have Alice (A) and Bob (B).

1.  [Init]
    A sends B: {_N<sub>A</sub>_, _A_}<sub>_K<sub>B</sub>_</sub>, where A means just
    a name of author (Alice) and _N<sub>A</sub>_ is some random _unguessable_ number
    called **nonce**.

2.  [trans1]
    B sends A: {_N<sub>B</sub>_, _N<sub>A</sub>_}<sub>_K<sub>A</sub>_</sub>.
    
3.  [trans2]
    A sends B: {_N<sub>B</sub>_}<sub>_K<sub>B</sub>_</sub>.
    
We have mutual authentification here: A sure that B is B and vice versa. This is
example of authentification by knowledge.
    
We say that protocol is _network insecure_ if one of properties holds:

* attacker can eavesdrop messages,
* attacker can massage (modify and resend) messages.

Particular problems that can evolve:

* nonce disclosure,
* masquerading (someone can prove that his is Alice).

We formilize the above described protocol as it is shown in example file for this lecture. Then we explore the attack invented by Gavin Love.

1. [init] A sends I:  {_N<sub>A</sub>_, _A_}<sub>_K<sub>I</sub>_</sub>.
2. [init'] I sends B: {_N<sub>A</sub>_, _A_}<sub>_K<sub>B</sub>_</sub> (begins
   masquerading).
3. [trans1] B sends I: {_N<sub>B</sub>_, _N<sub>A</sub>_}<sub>_K<sub>A</sub>_</sub>.
4. [trans1'] I sends A: {_N<sub>B</sub>_, _N<sub>A</sub>_}<sub>_K<sub>A</sub>_</sub>.
5. [trans2] A sends I: {_N<sub>B</sub>_}<sub>_K<sub>I</sub>_</sub>.
6. [trans2'] I sends B: {_N<sub>B</sub>_}<sub>_K<sub>B</sub>_</sub>.

We can model this attack with Coq (see examples to this lecture). To protect the
scheme we need to add third parameter to `trans1` phase: the  author of a 
message. 

Then we want to prove that nonce disclosure could not happen. For this we difine
an inductove type/set of all messages that could be known publicly and prove
that the nonce is not in it.

THen we want to exclude the possibility of masquerading which is formulated as 
follows:

> if B recieves it's nonce at the end, he can be sure that the connection
> was initiated exactly for him.

This statement is the direct conclusion from the scheme of attack given above,
which looked like: A sends to I smth … I sends to B its nonce.

## Home task

* To automate all the proofs in examples to this lecture as much as possible.


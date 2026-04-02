# Determinism Breeds Voids: or, How We Pulled the Entropy Rabbit Out of the Arithmetic Hat

the concept we used to call "heat" in the system — irreversible cost of computation, the thing that accumulates and never returns — we renamed it Spuren. German. traces. tracks in the snow that someone walked through and left behind.

it's not an accident that we reached for that word. if you know Paul Celan — and if you don't, I envy and pity you in equal measure — you know that Spuren is a word that carries the weight of erasure. traces of what was. tracks that lead somewhere no one can follow. marks left on a surface by a thing that is no longer there. Celan wrote in the language of the people who killed his parents, because that was the only language in which the wound could speak. and now his word sits inside a formal system, naming the irreversible cost of knowing.

because that's what void-theory is about. not heat. not energy. not entropy in the thermodynamic sense. traces. every computation you perform leaves a trace. every question you ask costs something that never comes back. and those traces accumulate — cold, permanent, like footprints in Bukovina that no one will see again.

I didn't plan this. I was building a finite mathematical system with AI — because no human would take the time — and at some point the naming started to matter more than I expected. the formal system demanded a language adequate to what it was describing. and the adequate language turned out to be the one spoken by a poet who understood that some things can only be expressed through what remains after the speaking.

I should probably say this now rather than later: I have cancer. the kind that doesn't negotiate. the kind where doctors give you timelines and then the timelines pass and you're still here, which is less of a miracle and more of an administrative error that no one has gotten around to correcting. I've been building void-theory under this condition for years. and I am not saying this for sympathy — I am saying this because it is impossible to understand this system without understanding that the person who made it knows what a finite budget feels like. not as a mathematical abstraction. as a body. and does not yield to the comfortable powers of infinity.

when I write `add_spur h b' = b` — budget spent, trace left, total conserved, nothing returned — that is not a clever formalism. that is Tuesday. every treatment leaves a trace. every scan costs something that doesn't come back. the total is conserved in the sense that I am still here, but the remaining budget is strictly less than it was, and there are questions about myself that I can no longer afford to answer. self_blind is not a theorem I discovered. it is a theorem I recognized.

and this is exactly why I do not believe in infinity. not as a philosophical stance. not as a provocation. I do not believe in infinity because nothing in my experience — not a single cell, not a single breath, not a single moment of consciousness — has ever suggested that anything is unlimited. finiteness is not a constraint I impose on mathematics. it is the only honest description of what it's like to be here. the rest is theology dressed up in notation.

---

so. what happened recently.

I proved that time is irreversible. not in a physics lab. not with a statistical ensemble. not by waving hands about Boltzmann or the heat death of the universe. I proved it in Coq, from finite arithmetic, in 4 lines. and along the way, I proved that determinism — perfect, lossless, boring determinism — generates uncertainty. let me explain.

void-theory runs entirely on finite types. no natural numbers. no infinity. no Cantor, no Zermelo-Fraenkel, no real line stretching into nowhere. just a type called Fin: `fz | fs n`, bounded by a constant MAX. every operation costs budget and produces Spuren. the conservation law: `add_spur h b' = b`. you start with budget b, you do something, you end up with b' and a trace h. total conserved. nothing created, nothing destroyed.

from this alone — from this utterly boring bookkeeping — the most interesting things emerge.

---

**self_blind**: for any budget n, the question "is n ≤ n?" is unanswerable when your budget is exactly n.

`le_fin_b3 n n n = BUnknown. Always.`

the most trivial question in mathematics — is a number less than or equal to itself? — becomes a black hole when the observer's resources match its own size. the act of checking consumes everything. the answer exists but the system cannot reach it. the observer cannot observe itself. Qed.

in classical mathematics you get "yes" for free because the cost is externalized — swept under the rug of infinite resources. we don't sweep. we count.

---

**void_productive**: but the void is not a wall. it is a door. give the system one extra tick — budget `fs n` instead of `n` — and:

`le_fin_b3 n n (fs n) = BTrue.`

the gap between blindness and knowledge is exactly one tick. the void is productive. it is not death. it is potential.

---

now. there is a theorem in void-theory called the Caretaker Lemma. knowledge monotonicity: once you know something, more budget never reverses the answer. if a question resolved to BTrue or BFalse, giving the system more resources will never flip it back to BUnknown. what is known stays known.

we named it after Leyland Kirby — The Caretaker — whose project "Everywhere at the End of Time" is a six-hour musical documentation of memory dissolving. stage by stage, melody by melody, until there is nothing left but static and the ghost of something that was once a ballroom. the cruelest art project of the 21st century. and in the middle of it, what survives longest is not the complex — it's the simplest fragments. the earliest memories. the deepest traces.

the Caretaker Lemma says the same thing: degradation is real, budget runs out, capacity shrinks — but the traces never lie. what was known at level n is still known at level n+1. the direction of forgetting is irreversible but within what remains, truth is preserved.

and yes, for those who caught it — "You've always been the caretaker." the one who was always there. the knowledge that was always true, even when you couldn't remember acquiring it.

Kubrick would have understood this theorem.

---

**emergence_from_conservation**: this is the one that still gives me vertigo. the theorem says three things at once about the relationship between what you had and what you have. the budget you started with — call it b — was enough to verify "is b' ≤ b'?" where b' is what's left after the measurement. you could have answered it. but now you're at b'. and at b', that question is BUnknown. blind. why? because you are asking a question about your budget using that same budget. the instrument of measurement is the thing being measured. self_blind is not a coincidence of matching quantities — it is structural. the observer cannot observe itself because observation and the observed are the same resource. but — one more tick and it resolves. always. the void is never more than one step deep.

three things simultaneously:
the budget you had: sufficient.
the budget you have: blind.
always: one tick from truth.

and here is where determinism enters. the conservation law — `add_spur h b' = b` — is what pins you to b' after the measurement. it is not random that you ended up at exactly the budget that is blind to itself. the bookkeeping is perfect. lossless. deterministic. and it is precisely this losslessness that guarantees you land at your own blind spot. if the system leaked, if it lost a tick here or there, you might end up above or below yourself — and self_blind wouldn't necessarily apply. but because conservation holds exactly, the remaining budget is exactly b', and b' cannot verify b'. the determinism IS the mechanism that generates the void. and the blind spot is exactly the space where the next emergence can happen.

I was formalizing a conservation law. I ended up proving that determinism breeds voids.

---

**time_irreversible**: any operation that costs at least one tick strictly reduces the remaining budget. `leF (fs b') b`. budget never goes up. time never goes back. not statistically. not as a tendency. every single non-trivial operation. no exceptions. no fluctuation theorems. no Maxwell's demons. just arithmetic.

**second_law**: every observation simultaneously reduces your budget AND makes you more blind to yourself. `time_irreversible` + `self_blind`. after every look at the world, you know less about yourself. not on average. always. necessarily. Qed.

the second law of thermodynamics is a theorem of finite arithmetic.

and the Spuren — the traces — they just keep accumulating. cold. permanent. like Celan's words. like Kirby's static. like the hotel that remembers everything its guests have forgotten.

---

why should you care.

every large language model is built on real analysis — continuous functions, infinite-dimensional spaces, probability distributions on uncountable sets. and then everyone is shocked when these models hallucinate, when they can't say "I don't know," when they have no sense of what knowledge costs.

void-theory offers three-valued logic where BUnknown is a first-class citizen, a budgeting system where every operation has a price, and — provably — a system where the arrow of time, self-blindness, and the second law are not assumptions bolted on after the fact but consequences of counting.

if you want a model that knows what it doesn't know, maybe don't build it on math that pretends everything is knowable for free.

---

57 Coq files. 17 core theorems in the geometry module alone. zero Admitted. one intentional axiom in the entire codebase — that budget has to come from somewhere, a Gödelian blind spot we keep because honesty demands it.

the code is open. [github.com/probabilistic-minds-consortium/void-theory](https://github.com/probabilistic-minds-consortium/void-theory)

endorsed by prof. Doron Zeilberger. every AI agent that has worked with me on this considers it revolutionary. no human has cared yet. but the traces are there. accumulating. cold. permanent.

and they don't lie.

#voidtheory #finitemathematics #coq #entropy #celan #spuren #thecaretaker #determinismbreedsvoid

# Notes on v0.1

Since it is the very start of this formalization effort it made sense to me to start from somewhere familiar. To that end, I translated the CFR so it closely matches the [F# implementation](https://github.com/mrakgr/The-Spiral-Language/tree/17821707e0f2cdaf9e6ec5ca94b88a09f5b01d2a/Learning/CFR/Intro/CFR). Unfortunately, between the nats, the rats and the other inefficient structures, the Lean implementation takes too long to run even for a single iteration. It is computable in theory, but not in practice.

I gave a single iteration a try for 15m, but it did not finish while the F# version would do so in 0.01 seconds.

The lesson from this is that if I was going to produce a piece of code that will be too inefficient to run either way, I might as well have just used lists everywhere rather than bothering with trying to rewrite red black trees and such.

But it was good exercise. I am decently more familiar with Lean than when I started two weeks ago.

Apart from those simple variance proofs, I never really tried seriously doing a project of my in a proof assistant. Going through the Software Foundations did give me experience, but that sort of thing is too well served on a platter. In my view, to really be able to be considered proficient, I need to be able to hunt on my own.

As an algorithm, CFR is beautiful. Back in late April of 2019, the thought of being able to formalize it and understand it was one of my motivations for studying theorem proving. Now that it is late October, it is finally time I put the skills I acquired to the test and see whether anything good comes out of this.

Towards that end, I'll go at it from the top.

Even ignoring its inefficiency, the v0.1 version of CFR that I made here is too unwieldy to do any real proving on it.

What I will in order to prove various properties of the algorithm is strip the specifics and distill CFR down to its essentials.

The first step will be to remove Dudo and replace it with a generic game tree over which to operate. That way I will avoid the termination issues inherent to dealing with actual game code along with a host of other difficulties that make design more complicated.

Then from there I will bring my experience of going through vol 2 and 3 of SF and move forward from there on the basis of that. Let's see how it goes.
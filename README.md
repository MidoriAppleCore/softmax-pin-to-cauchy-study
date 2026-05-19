# Softmax pin to Cauchy-Poisson Study

find place where two things fit, pin them together;
open the door;
you can make it act the same, and it has to act the same;
understand that it's forced in this regeime to be our geometry;
walk through, close the door, mark it as a degenerate part of the geometry;
then you have a whole expressive world in front of you, with poles you can constrain any way you want, ways to understand groups and symmetries in attention mechanisms;
from what i understand. the lean only proves the 'single particle universe' version of this. pytorch tests show its what you'd expect though

Basically, you can lift out into cauchy-kernel then start designing attention kernels with other constraints than the constraint to softmax.

I think this lets you do manifold programming, like, if you wanted to model the english language in c++ with knowledge, you would be forced to have giant lists/matrices of floats, in a way, then is AI how you derive those floats? would we feed attention kernal outputs into inputs in a node chart, with those being of groups that have some relation to how you would solve some problem whilst programming?

Softmax transformers have the capabilities of turing machines, then they can emulate any set of groups of whatever sequences, then the methods of the field are good enough to generate entire manifold programs, but theres probably an emulation tax involved.

This project is released under the [MIT License](LICENSE).

## Lean / Lake

All Lean sources sit next to `lakefile.toml`. **Do your Lean work here** — you do not need to open a Nix shell from the parent `mathgame` repo unless you are also hacking the web client.

### Option A — elan already on your PATH (simplest)

```bash
cd transformers-are-cauchy-poisson   # wherever you cloned it
elan toolchain install "$(tr -d '\n' < lean-toolchain)"   # once per machine
lake update && lake build && lake exe transformers
```

### Option B — Nix, from **this** directory

```bash
cd transformers-are-cauchy-poisson
nix develop   # or: nix-shell
lake update && lake build && lake exe transformers
```

Avoid **`nix-shell -p lean4`** here: it pins Nix’s Lean (often **4.20**) and fights Mathlib’s **`lean-toolchain`** (**4.21**). This repo’s shells only add **elan**.

### Parent repo `mathgame`

The browser game lives one level up. Use **`nix develop`** there when you need **Node + Vite + elan** together (e.g. `npm run dev` and Lean in one session). For **Lake builds only**, staying in **this** folder is enough.

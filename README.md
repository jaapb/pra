Primitive recursive arithmetic plugin for Coq

Running:
coq_makefile -f Make -o Makefile
make (this needs GNU make, so might be gmake on your system)

And then run coqide with the following flags:
coqide -R theories pra -I src theories/prime.v

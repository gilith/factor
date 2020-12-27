###############################################################################
# Documentation and profiling
###############################################################################

FACTOR = ../dist-newstyle/build/x86_64-linux/ghc-8.0.1/factor-1.1/x/factor/build/factor/factor

RUNHASKELL = runhaskell -i../src

DOC = \
  ecm-example.txt \
  ecm-param.txt \
  factor-usage.txt \
  nfs-example.txt \
  swinnerton-dyer.txt

PROFILE = \
  ecm-profile.txt \
  nfs-profile.txt

###############################################################################
# Phony targets
###############################################################################

.PHONY: default
default: doc profile

.PHONY: doc
doc: $(DOC)

.PHONY: profile
profile: $(PROFILE)

.PHONY: clean
clean:
	rm -f $(DOC) $(PROFILE)

###############################################################################
# Documentation
###############################################################################

ecm-example.txt: $(FACTOR)
	/usr/bin/time $(FACTOR) -v --ecm-primes - 40583960879376931768709021465702027 &>$@

ecm-param.txt: ecm-param.hs
	$(RUNHASKELL) $< >$@

factor-usage.txt: $(FACTOR)
	$(FACTOR) -h &>$@

nfs-example.txt: $(FACTOR)
	/usr/bin/time $(FACTOR) -v --ecm-primes 0 361913909399305266402579347 &>$@

swinnerton-dyer.txt: swinnerton-dyer.hs
	$(RUNHASKELL) $< >$@

###############################################################################
# Profiling
###############################################################################

.PRECIOUS: $(PROFILE)

ecm-profile.txt: factor-profile.hs
	$(RUNHASKELL) $< ECM $(FACTOR) >$@

nfs-profile.txt: factor-profile.hs
	$(RUNHASKELL) $< NFS $(FACTOR) >$@

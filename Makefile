SRCS = $(wildcard */*.lean */*/*.lean */*/*/*.lean */*/*/*/*.lean)
OBJS = $(SRCS:.lean=.olean)
DEPS = $(SRCS:.lean=.depend)

.PHONY: all clean

all: $(OBJS)

depends: $(DEPS)

%.depend: %.lean
	@echo $(<:.lean=.olean): `lean --deps $< | python relative.py`  > $@

# %.depend: ;

%.olean: %.lean %.depend
	lean --make $<
# 	sccache lean --make $<

clean:
	find . -name *.olean -delete
	find . -name *.depend -delete

.PRECIOUS: %.depend

include $(DEPS)

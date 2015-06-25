# Unix makefile for tigermain example

HOME=~
MOSMLHOME=/usr
MOSMLTOOLS=${MOSMLHOME}/bin/camlrunm $(MOSMLHOME)/share/mosml/tools
MOSMLLEX=${MOSMLHOME}/bin/mosmllex
MOSMLYACC=${MOSMLHOME}/bin/mosmlyac -v

GCC=gcc
CFLAGS= -g
MOSMLC=${MOSMLHOME}/bin/mosmlc -c -liberal
MOSMLL=${MOSMLHOME}/bin/mosmlc

# Unix
REMOVE=rm -f
MOVE=mv
EXEFILE=

# DOS
#REMOVE=del
#MOVE=move
#EXEFILE=.exe

.SUFFIXES :
.SUFFIXES : .sig .sml .ui .uo

GRALOBJS= tigerabs.uo tigergrm.uo tigerlex.uo tigermain.uo \
	tigernlin.uo tigerpp.uo tigerescap.uo tigertab.uo tigerseman.uo tigertemp.uo topsort.uo tigertree.uo \
	tigerframe.uo tigertrans.uo tigerit.uo tigerpila.uo tigercanon.uo

all: tiger

tiger: $(GRALOBJS) $(OBJSGEN)
	$(MOSMLL) -o tiger $(EXEFILE) tigermain.uo

tigergrm.sml tigergrm.sig: tigergrm.y 
	$(MOSMLYACC) tigergrm.y

tigerlex.sml: tigerlex.lex
	$(MOSMLLEX) tigerlex.lex

clean:
	$(REMOVE) Makefile.bak
	$(REMOVE) tigergrm.output
	$(REMOVE) tigergrm.sig
	$(REMOVE) tigergrm.sml
	$(REMOVE) tigerlex.sml
	$(REMOVE) tigermain
	$(REMOVE) *.ui
	$(REMOVE) *.uo
	$(REMOVE) errlist
	$(REMOVE) *.o

.sig.ui:
	$(MOSMLC) $<

.sml.uo:
	$(MOSMLC) $<

depend: tigerabs.sml tigergrm.sml tigerlex.sml tigermain.sml \
	tigernlin.sml tigerpp.sml
	$(REMOVE) Makefile.bak
	$(MOVE) Makefile Makefile.bak
	$(MOSMLTOOLS)/cutdeps < Makefile.bak > Makefile
	$(MOSMLTOOLS)/mosmldep >> Makefile

### DO NOT DELETE THIS LINE
tigermain.uo: tigerseman.ui tigerescap.ui tigergrm.ui tigerlex.uo \
    tigerpp.uo 
tigerescap.uo: tigerescap.ui tigertab.ui tigerabs.uo 
tigerseman.uo: tigerseman.ui tigersres.uo tigertab.ui tigerpila.ui \
    topsort.uo tigertemp.ui tigerabs.uo tigertrans.ui 
tigertemp.uo: tigertemp.ui 
tigertrans.uo: tigertrans.ui tigertree.uo tigerpila.ui tigerframe.ui \
    tigerit.uo tigercanon.ui tigertemp.ui tigerabs.uo 
tigerpila.uo: tigerpila.ui 
tigerframe.uo: tigerframe.ui tigertree.uo tigertemp.ui 
tigergrm.uo: tigergrm.ui tigernlin.uo tigerabs.uo 
tigerframe.ui: tigertree.uo tigertemp.ui 
tigerpp.uo: tigerabs.uo 
tigerescap.ui: tigerabs.uo 
tigerlex.uo: tigergrm.ui tigernlin.uo 
tigertab.uo: tigertab.ui 
tigercanon.ui: tigertree.uo tigertemp.ui 
tigerseman.ui: tigerabs.uo 
tigertree.uo: tigertemp.ui 
tigerinterp.uo: tigertree.uo tigertab.ui tigerframe.ui tigerit.uo \
    tigertemp.ui 
tigertrans.ui: tigertree.uo tigerframe.ui tigertemp.ui tigerabs.uo 
tigercanon.uo: tigercanon.ui tigertree.uo tigertab.ui tigertemp.ui 
tigerit.uo: tigertree.uo tigertab.ui 
tigersres.uo: tigertab.ui tigertips.uo tigertemp.ui tigerabs.uo \
    tigertrans.ui 
tigergrm.ui: tigerabs.uo 

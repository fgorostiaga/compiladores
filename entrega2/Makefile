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
	tigerframe.uo tigertrans.uo tigerit.uo tigerpila.uo tigercanon.uo tigercodegen.uo \
	tigermakegraph.uo tigerflow.uo tigergraph.uo

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
tigerseman.uo: tigerseman.ui tigercodegen.ui tigersres.uo tigertab.ui \
    tigerpila.ui topsort.uo tigerassem.uo tigerinterp.uo tigermakegraph.ui \
    tigertemp.ui tigerabs.uo tigertrans.ui 
tigerassem.uo: tigertemp.ui 
Listsort.uo: Listsort.ui 
tigertemp.uo: tigertemp.ui 
tigertrans.uo: tigertrans.ui tigertree.uo tigerpila.ui tigerframe.ui \
    tigerit.uo tigercanon.ui tigertemp.ui tigerabs.uo 
tigerpila.uo: tigerpila.ui 
tigerframe.uo: tigerframe.ui tigertree.uo tigerassem.uo tigertemp.ui 
tigersimpleregalloc.uo: tigersimpleregalloc.ui tigerassem.uo 
tigersimpleregalloc.ui: tigerframe.ui tigerassem.uo 
tigergrm.uo: tigergrm.ui tigernlin.uo tigerabs.uo 
tigerframe.ui: tigertree.uo tigerassem.uo tigertemp.ui 
tigerpp.uo: tigerabs.uo 
tigerflow.uo: tigerflow.ui 
tigercodegen.ui: tigerframe.ui tigerassem.uo 
tigercodegen.uo: tigercodegen.ui tigertree.uo tigerframe.ui tigerassem.uo \
    tigertemp.ui 
tigergraph.ui: tigertab.ui 
tigerescap.ui: tigerabs.uo 
tigerlex.uo: tigergrm.ui tigernlin.uo 
tigertab.uo: tigertab.ui 
tigermakegraph.ui: tigerassem.uo tigerflow.ui 
tigercanon.ui: tigertree.uo tigertemp.ui 
tigerseman.ui: tigerabs.uo 
tigertree.uo: tigertemp.ui 
tigerinterp.uo: tigertree.uo tigertab.ui tigerframe.ui tigerit.uo \
    tigertemp.ui 
tigertrans.ui: tigertree.uo tigerframe.ui tigertemp.ui tigerabs.uo 
tigermakegraph.uo: tigermakegraph.ui tigerflow.ui 
tigercanon.uo: tigercanon.ui tigertree.uo tigertab.ui tigertemp.ui 
tigerit.uo: tigertree.uo tigertab.ui 
tigerflow.ui: tigergraph.ui tigertemp.ui 
tigersres.uo: tigertab.ui tigertips.uo tigertemp.ui tigerabs.uo \
    tigertrans.ui 
tigergrm.ui: tigerabs.uo 

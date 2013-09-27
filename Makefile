BINDIR=./bin
SRCDIR=./src
TARGET=pave
BINNAME=pave

.PHONY: all clean install

all: $(SRCDIR)/$(TARGET)

$(SRCDIR)/$(TARGET): 
	$(MAKE) -C $(SRCDIR)

install: all
	mkdir -p $(BINDIR)
	cp $(SRCDIR)/$(TARGET) $(BINDIR)/$(BINNAME)

clean:
	$(MAKE) -C $(SRCDIR) clean

very-clean: clean
	rm -rf $(BINDIR)

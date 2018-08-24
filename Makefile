include config.mk

SUBDIRS := erc20 erc20_burnable erc20_pausable erc20_mintable erc20_lockable
SUBDIRS += erc20_upgradable
SUBDIRS += erc721

all: $(SUBDIRS)
	@for dir in $(SUBDIRS); do \
		echo "+" $$dir; \
		$(MAKE) -C $$dir -f Makefile $@; \
	done

clean: $(SUBDIRS)
	@for dir in $(SUBDIRS); do \
		echo "+" $$dir; \
		$(MAKE) -C $$dir -f Makefile $@; \
	done
	@find libs -name ".*.aux" -delete
	@find libs -name ".*.d" -delete

.PHONY: all clean

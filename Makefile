include config.mk

SUBDIRS := erc20 erc20_burnable erc20_pausable

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

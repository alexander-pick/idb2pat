PROC=idb2pat
!include ..\plugin.mak

CPP_PROJ=/D "_CRT_SECURE_NO_DEPRECATE" /D "USE_DANGEROUS_FUNCTIONS"

# MAKEDEP dependency list ------------------
$(F)idb2pat$(O)   : $(I)ida.hpp $(I)loader.hpp $(I)kernwin.hpp        \
	         		$(I)diskio.hpp $(I)idp.hpp $(I)auto.hpp	$(I)ua.hpp				\
					$(I)bytes.hpp $(I)name.hpp $(I)entry.hpp $(I)funcs.hpp \
					$(I)expr.hpp $(I)fpro.h $(I)diskio.hpp idb2pat.cpp

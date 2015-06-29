# MITL2Timed makefile based on LTL2BA (See original comments below.)
#
# ARC; May 22 2015.

# LTL2BA - Version 1.0 - October 2001
# Written by Denis Oddoux, LIAFA, France                                 
# Copyright (c) 2001  Denis Oddoux                                       
#                                                                        
# This program is free software; you can redistribute it and/or modify   
# it under the terms of the GNU General Public License as published by   
# the Free Software Foundation; either version 2 of the License, or      
# (at your option) any later version.                                    
#                                                                        
# This program is distributed in the hope that it will be useful,        
# but WITHOUT ANY WARRANTY; without even the implied warranty of         
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the          
# GNU General Public License for more details.                           
#                                                                        
# You should have received a copy of the GNU General Public License      
# along with this program; if not, write to the Free Software            
# Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA
#                                                                        
# Based on the translation algorithm by Gastin and Oddoux,               
# presented at the CAV Conference, held in 2001, Paris, Fance 2001.     
# Send bug-reports and/or questions to: Denis.Oddoux@liafa.jussieu.fr    
# or to Denis Oddoux                                                     
#       LIAFA, UMR 7089, case 7014                                       
#       Universite Paris 7                                               
#       2, place Jussieu                                                 
#       F-75251 Paris Cedex 05                                          
#       FRANCE                                                               

# -ansi is removed and -sd=c11 is added to use comment // and for-loop with initialization

CC=gcc
# CFLAGS= -O3 -g -DNXT -DTIMED
CFLAGS= -g -DNXT -std=c11
MITL2TA= parse.o lex.o main.o trans.o buchi.o set.o mem.o rewrt.o cache.o alternating.o generalized.o timed.o

mitl2ta: $(MITL2TA)
	$(CC) $(CFLAGS) -o mitl2ta $(MITL2TA) -lm

$(MITL2TA): ltl2ba.h

clean:
	rm -f MITL2TA *.o core

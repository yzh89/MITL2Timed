#!/usr/bin/python

# this is to test the python api to create the xml files should be auto generated
from pyuppaal import *

def main():
	locid = 0
	locations = []

	locations.append( Location(invariant="x>=5", urgent=False, committed=False, name='loc 1', id = 'id'+str(locid),
	        xpos=0, ypos=0) )

	locid +=1

	locations.append( Location(invariant="x>=6", urgent=False, committed=False, name='loc 2', id = 'id'+str(locid),
	        xpos=0, ypos=0) )

	locid +=1


	transitions = []
	transitions.append( Transition(locations[0], locations[1], guard="x>5", 
		assignment="x=0") )
	transitions.append( Transition(locations[1], locations[0], guard="x>6", 
		assignment="x=0") )

	template = Template('sys1', locations=locations, transitions=transitions, declaration="clock x;", initlocation=locations[0])

	nta = NTA(system = "system sys1;", templates=[template])

	print nta.to_xml()


if __name__ == "__main__":
    main()
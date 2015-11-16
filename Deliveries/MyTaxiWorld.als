 
	//Alloy Model for MyTaxiService	

	//Datatype representing alphanumeric strings
	one sig Strings{}	

	//Datatype representing boolean values
	one sig Boolean{}

	//Datatype representing dates 
	sig DateTime{}

	//Datatype representing birthdays
	one sig DateBirthday{}

	//Datatype representing positions of cab catchers
	sig Position{}

	//Datatype representing boundaries of zones
	one sig Perimeter{}

	//The zones in which the city is divided
	some sig Zone{
					zonePerimeter: one Perimeter
					}

	//The taxi queues to which zones are related
	sig TaxiQueue{
			zone: one Zone
			}

	//The taxies of the city
	some sig Taxi{
			queue: lone TaxiQueue,
			code: one Strings,
			after: lone Taxi
			}
	
	//The taxi drivers
	sig CabDriver{
			taxi: one Taxi,
			firstName: one Strings,
			lastName: one Strings,
			username: one Strings,
			password: one Strings,
			phoneNumber: one Strings,
			email: one Strings,
			sex: one Strings,
			dateOfBirth: one DateBirthday
			}
	//The taxi potential passengers	
	sig CabCatcher{
			firstName: one Strings,
			lastName: one Strings,
			username: one Strings,
			password: one Strings,
			phoneNumber: one Strings,
			email: one Strings,
			sex: one Strings,
			dateOfBirth: one DateBirthday,
			catcherPosition: one Position
			}
	//The passenger requests
	sig Request{
			requestPassenger: one CabCatcher,
			requestDriver: lone CabDriver,
			requestAPI: one Boolean,
			timeOut: one DateTime
			}
’
	//The passenger reservations
	sig Reservation{
			reservationPassenger: one CabCatcher,
			reservationDriver: lone CabDriver,
			meetingTime: one DateTime,
			originPoint: one Position,
			destinationPoint: one Position,
			reservationAPI: one Boolean,
			timeOut: one DateTime
			}

	//Position is a data type associated with cab catchers, it has to be present only if there is at least a cab catcher
	fact{
			some CabCatcher implies #Position = 1 else #Position = 0
			}

	//DateTime is a data type associated with reservations, it has to be present only if there is at least a reservation
	fact{
			(some Reservation or some Request) implies (#DateTime = 1 and #Boolean = 1) else (#DateTime = 0 and #Boolean = 0)
			}

	//Each cab driver who has taken care of a request is no more related to a taxi queue (unavailable)
	fact{
			all r: Request, t: Taxi | (some r.requestDriver and r.requestDriver.taxi = t) implies #t.queue = 0
			}

	//Each taxi that is not implicated in an arrangement is related to a taxi queue (available)
	fact{
			all t: Taxi | (t not in (Request.requestDriver.taxi + Reservation.reservationDriver.taxi)) implies #t.queue = 1
			} 	

	//Each cab driver who has taken care of a reservation is no more related to a taxi queue (unavailable)
	fact{
			all r: Reservation, t: Taxi | (some r.reservationDriver and r.reservationDriver.taxi = t) implies #t.queue = 0
			}

	//Each zone has exactly a taxi queue
	fact{
			all z: Zone | #z.~zone = 1
			}

	//Each taxi has exactly a cab driver
	fact{
			all t: Taxi | #t.~taxi = 1
			}
	
	//The queues are composed of taxies that are linked according the "after" relationship
	fact{
			all t: Taxi | t not in TaxiQueue.~queue implies #(t.after) = 0 and #(t.~after) = 0
			all t: Taxi, q: TaxiQueue | t in q.~queue and #(q.~queue) > 1 implies #(t.after + t.~after) >= 1
			all t: Taxi | t->t not in ^after
			all t: Taxi | t.after != t
			all q: TaxiQueue | #q.~queue != 0 implies (q.~queue.after.queue in q) and  #( q.~queue - q.~queue.after) = 1
			all q: TaxiQueue | #q.~queue != 0 implies #( q.~queue - q.~queue.~after) = 1
			}

	//The number of cab drivers must be greater than or equal to the number of requests, due to the domain assumptions
	fact{
			#CabDriver >= #Request
			}
	//Each cab catcher can make only one request per time
	fact{
			all c: CabCatcher | #c.~requestPassenger =< 1
			}

	//Each cab catcher can't have both an allocated reservation and an allocated request
	fact{
			all c: CabCatcher | some (c.~reservationPassenger.reservationDriver) implies  #(c.~requestPassenger.requestDriver) = 0
			}
	//Each cab catcher can't have both an allocated reservation and an allocated request
	fact{
			all c: CabCatcher | some (c.~requestPassenger.requestDriver) implies #(c.~reservationPassenger.reservationDriver) = 0
			}

	//Each cab catcher can't have more than one allocated reservation
	fact{
			all c: CabCatcher | #(c.~reservationPassenger.reservationDriver)  =<1
			}
	//Each cab driver can't handle more than one arrangement per time
	fact{
		all c: CabDriver | #(c.~requestDriver + c.~reservationDriver) =< 1
			}

	//Predicate to make a request
	pred makeRequest[c, c': CabCatcher, r: Request]{
			c != c'
			#c.~reservationPassenger = #c'.~reservationPassenger
			r.requestDriver = none
			c'.~requestPassenger = c.~requestPassenger + r
			}

	run makeRequest for 3

	//Predicate to make a reservation
	pred makeReservation[c, c': CabCatcher, r: Reservation]{
			c != c'
			r.reservationDriver = none
			#c.~requestPassenger = #c'.~requestPassenger
			c'.~reservationPassenger = c.~reservationPassenger + r
			}

	run makeReservation for 5

	//Predicate to delete a request
	pred deleteRequest[c,c': CabCatcher, r: Request]{
			r in (c.~requestPassenger)
			#c.~reservationPassenger = #c'.~reservationPassenger
			c'.~requestPassenger = (c.~requestPassenger - r) 
			}
	
	run deleteRequest for 5

	//Predicate to delete a reservation
	pred deleteReservation[c,c': CabCatcher, r: Reservation]{
			r in (c.~reservationPassenger)
			#c.~requestPassenger = #c'.~requestPassenger
			c'.~reservationPassenger = (c.~reservationPassenger - r) 
			}
	
	run deleteReservation for 2

	//Predicate to allocate a reservation to a cab driver
	pred allocateReservation[c: CabDriver, r, r': Reservation]{
			r.reservationDriver = none
			r'.reservationPassenger = r.reservationPassenger
			r'.meetingTime = r.meetingTime 
			r'.originPoint = r.originPoint
			r'.destinationPoint = r.destinationPoint
			r'.reservationDriver = c
			}
	
	run allocateReservation for 3

	//Check that the number of request is lower than or equal to the number of cab catchers
	assert lowerRequests{
										#Request <= #CabCatcher
									}

	check lowerRequests for 5

	//Check the makeRequest predicate
	assert addRequest{
									all c1, c2: CabCatcher, r: Request | makeRequest[c1,c2,r] implies (r in (c2.~requestPassenger)) and (r not in (c1.~requestPassenger))
									all c1, c2: CabCatcher, r: Request | makeRequest[c1,c2,r] implies c1.~requestPassenger = none
									}

	check addRequest for 5

	//Check the makeReservation predicate
	assert addReservation{
									all c1, c2: CabCatcher, r: Reservation | makeReservation[c1,c2,r] implies (r in (c2.~reservationPassenger)) and (r not in (c1.~reservationPassenger))
									}

	check addReservation for 5

	//Check the deleteRequest predicate
	assert cancelRequest{
										all c1, c2: CabCatcher, r: Request | deleteRequest[c1,c2,r] implies (r not in (c2.~requestPassenger)) and c1 != c2
										}
	
	check cancelRequest for 5

	//Check the deleteReservation predicate
	assert cancelReservation{
											all c1, c2: CabCatcher, r: Reservation | deleteReservation[c1,c2,r] implies (r not in (c2.~reservationPassenger)) and c1 != c2
											}
	
	check cancelReservation for 5

	//Check the allocateReservation predicate
	assert assignReservation{
											all c: CabDriver, r1, r2: Reservation | allocateReservation[c,r1,r2] implies r1 != r2 and #c.~reservationDriver = 1
											}

	check assignReservation for 5
	

pred showWorld { }

run showWorld for 3 but 2 CabCatcher, 2 Reservation, 2 Request

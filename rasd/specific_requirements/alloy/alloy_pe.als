open util/boolean

//UNIX time notation is used
//Dates are calculated as the number of seconds from the 1st of January 1970

sig StringPE {}

sig User {
	email: one Int, //email is modeled as an Int to allow comparisons
	name: one StringPE,
	surname: one StringPE,
	idCardNumber: one Int,
	taxCode: one Int,
	licenseIdNumber: one Int,
	address: one StringPE,
	phoneNumber: one Int,
	paymentMethod: one PaymentMethod,
	isAccountLocked: Bool,
	userPosition: lone Position,
} {
	email > 0
	idCardNumber > 0
	taxCode > 0
	licenseIdNumber > 0
	phoneNumber > 0
}

sig PaymentMethod {}

//isLocked = True sblocca la macchina se e solo se l'utente e' in prossimita'
//isEngineOn serve davvero? (forse per dire che isOnCharge implies (isEngineOn = false)
sig Car {
	carCode: one Int,
	status: one CarStatus,
	batteryLevel: one Int,
	isLocked: Bool,
	isEngineOn: Bool,
	isOnCharge: Bool,
	carPosition: one Position,
} {
	batteryLevel >= 0 and batteryLevel <= 100
	carCode > 0
}

abstract sig CarStatus {}
one sig AVAILABLE extends CarStatus {}
one sig OUTOFSERVICE extends CarStatus {}
one sig RESERVED extends CarStatus {}
one sig INUSE extends CarStatus {}

//Da usare per capire quando inizia e finisce una ride
abstract sig RideStatus {}
one sig AUTHENTICATED extends RideStatus{}
one sig COMPLETED extends RideStatus{}

sig Reservation {
	reservedCar: one Car,
	reservedUser: one User,
	reservationTime: one Int,
	expirationTime: one Int,
	unlockTime: lone Int,
	isActive: Bool,
	isExpired: Bool,
} {
	reservationTime > 0
	unlockTime > 0
	expirationTime > 0
	reservationTime < expirationTime
	reservationTime < unlockTime
	unlockTime < expirationTime

	isExpired = True implies isActive = False
}

//RideCar LONE? perche' quando e' completata nessuna macchina e' piu' associata
sig Ride {
	reservation: one Reservation,
	rideCar: one Car,
	rideUser: one User,
	startTime: one Int,
	endTime: lone Int,
	originLocation: one Position,
	finalLocation: lone Position,
	rideStatus: one RideStatus,
	standardCharges: one Int,
} {
	startTime < endTime
	startTime > reservation.unlockTime
	standardCharges >= 0	

	reservation.isActive = False
	reservation.isExpired = False

	originLocation in SafeArea.coverage
}

sig Float {}

sig PowerGridStation {
	location: Position,
}

sig Position {
	latitude: one Float,
	longitude: one Float,
}

//The Safe Area is unique
one sig SafeArea {
	coverage: set Position,
} {
	#coverage>0
}

sig Payment {
	payRide: lone Ride,
	payRes: lone Reservation,
	totalAmount: one Int,
	isPending: Bool,
} {
	totalAmount > 0
	one payRide implies no payRes
	one payRes implies no payRide
}

//no two coinciding but distinct positions
fact NoPositionOverlapping {
	no disj p1, p2: Position | (p1.latitude = p2.latitude and p1.longitude = p2.longitude)
}

fact UniqueUser {
	no disj u1, u2: User | (u1 != u2 and
		(u1.email = u2.email or u1.idCardNumber = u2.idCardNumber or
		u1.taxCode = u2.taxCode or u1.licenseIdNumber = u2.licenseIdNumber))
}

//no two active reservations by the same user
fact UniqueReservation {
	no disj res1, res2: Reservation | (res1 != res2 and
		(res1.reservedUser = res2.reservedUser and res1.isActive = True
		and res2.isActive = True))
}

//TODO: stessa macchina, al massimo una reservation/ride per volta

//TODO: stesso user, no due ride nello stesso momento?

//no users con account bloccato hanno active reservations
fact NoBlockedUserReservation {
	no res: Reservation | (res.reservedUser.isAccountLocked = True)
}

fact UniqueCarCode {
	no disj c1, c2: Car | (c1 != c2 and c1.carCode = c2.carCode)
}

fact AvailableForRentCar {
	all c: Car | (c.status = AVAILABLE)
		<=> (c.batteryLevel > 20 and c. isLocked = True and c.isEngineOn = False
			and c.carPosition in SafeArea.coverage and 
			(no r: Reservation | (r.reservedCar = c)))
}

//Quando la macchina e' reserved
fact ReservedCar {
	all c: Car | (c.status = RESERVED)
		implies ((one res: Reservation | res.reservedCar = c) and 
			c.batteryLevel > 20 and c. isLocked = True and c.isEngineOn = False)
}

//TODO: quando la macchina e' INUSE (da completare!)
fact InUseCar {
	all c: Car | (c.status = INUSE)
		implies (c.isLocked = False and c.isOnCharge = False and c.batteryLevel > 0)
}

//TODO: quando la macchina e' Out-Of-Service (da completare!)
fact OutOfServiceCar {
	all c: Car | (c.status = OUTOFSERVICE)
		implies (c.isEngineOn = False and (c.isOnCharge = True implies c.isLocked = True))
}

//no two cars in the same position
fact NoCarPositionOverlapping {
	no disj c1, c2: Car | c1.carPosition = c2.carPosition
}

//no two users in the same position
fact NoUserPositionOverlapping {
	no disj u1, u2: User | u1.userPosition = u2.userPosition
}

//Da sistemare aggiungendo che ci deve essere una reservation associata
fact BeginRide {
	all r: Ride | (r.rideStatus = AUTHENTICATED)
		implies (r.rideUser = r.reservation.reservedUser and r.rideCar = r.reservation.reservedCar
			and one startTime and one originLocation)
}

fact NoOverlappingRidesPerUser {
	all disj r1, r2: Ride | ((r1 != r2 and r1.rideUser = r2.rideUser) implies
		(r1.endTime < r2.startTime or r2.endTime < r1.startTime))
}

fact PowerGridInsideSafeArea {
	all pgs: PowerGridStation | pgs.location in SafeArea.coverage
}

//No rides with expired reservations
fact NoRideIfReservationExpired {
	no r: Ride | (r.reservation.isExpired = True)
}

fact RideCompleted {
	all r: Ride | (r.rideStatus = COMPLETED) implies
		(one endTime and one finalLocation)
}

//Reservation expiration implies payment (fee)
fact ReservationExpirationPayment {
	all res: Reservation, p: Payment | (res.isExpired = True) implies
		(one p.payRes and p.payRes = res)
}

//NON FUNZIONA
//User account locked if pending payment
fact PendingPaymentsLockAccounts {
//	all p: Payment, res: Reservation, r: Ride | (p.isPending = True) <=>
//		((p.payRes.reservedUser.isAccountLocked = True and p.payRes = res) or 
//		(p.payRide.rideUser.isAccountLocked = True and p.payRide = r))
//}

//Bisogna modellare il fatto che se una ride finisce, la macchina torna available oppure no

//Quando lo stato della ride e' authenticated, la ride puo' iniziare (una posizione iniziale,
// ma non ancora una finale (posizione + time)

//Quando la ride finisce (ENDED), c'e' un luogo e un tempo

pred show() {
	//Funziona
	//some r: Reservation | r.isExpired = True
	//some u: User | u.isAccountLocked = True
}

run show for 4

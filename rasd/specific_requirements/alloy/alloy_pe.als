open util/boolean

//UNIX time notation is used
//Dates are calculated as the number of seconds from the
//		1st of January 1970

//------------SIGNATURES------------

//String abstraction
sig StringPE {}

sig User {
	//<<email>> is modeled as an Int to allow comparisons
	email: one Int,
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
}

sig PaymentMethod {}

sig Car {
	carCode: one Int,
	status: one CarStatus,
	batteryLevel: one BatteryLevel,
	isLocked: Bool,
	isEngineOn: Bool,
	isOnCharge: Bool,
	carPosition: one Position
} {
	carCode > 0
	status = AVAILABLE implies batteryLevel = HIGH
	status = RESERVED implies batteryLevel = HIGH
	status = INUSE implies not (batteryLevel = EMPTY)
	batteryLevel = EMPTY implies status = OUTOFSERVICE
	isOnCharge = True implies isLocked = True
	isOnCharge = True implies 
		(one pg: PowerGridStation | pg.location = carPosition)
}

abstract sig CarStatus {}
one sig AVAILABLE extends CarStatus {}
one sig OUTOFSERVICE extends CarStatus {}
one sig RESERVED extends CarStatus {}
one sig INUSE extends CarStatus {}

abstract sig RideStatus {}
one sig AUTHENTICATED extends RideStatus{}
one sig COMPLETED extends RideStatus{}

sig Reservation {
	reservedCar: one Car,
	reservedUser: one User,
	reservationTime: one Int,
	expirationTime: one Int,
	unlockTime: lone Int,
	//<<isActive = True>> until the car becomes "INUSE"
	isActive: Bool,
	isExpired: Bool,
	fee: lone Payment
} {
	reservationTime > 0
	unlockTime > 0
	expirationTime > 0
	reservationTime < expirationTime
	reservationTime < unlockTime
	unlockTime < expirationTime

	isExpired = True implies isActive = False
	one fee <=> isExpired = True
}

sig Ride {
	reservation: one Reservation,
	startTime: one Int,
	endTime: lone Int,
	originLocation: one Position,
	finalLocation: lone Position,
	rideStatus: one RideStatus,
	standardCharges: one Int,
	payment: lone Payment,
	discount: lone Discount,
	addCharges: set AdditionalCharge
} {
	rideStatus = COMPLETED <=> (startTime < endTime)
	startTime > reservation.unlockTime
	standardCharges > 0	

	//If a ride exists, its associated reservation is not active
	//		anymore!
	reservation.isActive = False
	reservation.isExpired = False

	originLocation in SafeArea.coverage
	not (finalLocation in SafeArea.coverage)
		implies (reservation.reservedCar.status = OUTOFSERVICE)
}

//Float abstraction
sig Float {}

sig PowerGridStation {
	location: Position,
}

sig Position {
	latitude: one Float,
	longitude: one Float,
}

//The Safe Area is UNIQUE
one sig SafeArea {
	coverage: set Position,
} {
	#coverage>0
}

sig Payment {
	totalAmount: one Int,
	//<<isPending = True>> if the system was not able
	//		to perform the payment
	isPending: Bool,
} {
	totalAmount > 0
}

abstract sig BatteryLevel {}
one sig EMPTY extends BatteryLevel {}
one sig LOW extends BatteryLevel {}
one sig HIGH extends BatteryLevel {}

abstract sig AlternativeChargesSituation {
	amount: one Int
}{
	amount > 0
}
sig Discount extends AlternativeChargesSituation {}
sig AdditionalCharge extends AlternativeChargesSituation {}


//------------FACTS------------

//AVAILABLE cars conditions
fact AvailableForRentCar {
	all c: Car | (c.status = AVAILABLE)
		implies (c. isLocked = True and c.isEngineOn = False
			and c.carPosition in SafeArea.coverage and 
			(no r: Reservation | r.reservedCar = c and
			r.isActive = True))
}

//RESERVED cars conditions
fact ReservedCar {
	all c: Car | (c.status = RESERVED)
		implies ((one res: Reservation | res.reservedCar = c 
							and (no r: Ride | r.reservation = res)
			and res.isActive = True)
			and c.carPosition in SafeArea.coverage
			and c.isLocked = True
			and c.isEngineOn = False)
}

//INUSE cars conditions
fact InUseCar {
	all c: Car | (c.status = INUSE)
		implies (c.isLocked = False and c.isOnCharge = False
			and (one r: Ride | r.rideStatus = AUTHENTICATED
						and r.reservation.reservedCar = c))
}

//OUTOFSERVICE cars conditions
fact OutOfServiceCar {
	all c: Car | (c.status = OUTOFSERVICE)
		implies (c.isEngineOn = False and
						(no res: Reservation | res.isActive = True
						and res.reservedCar = c))
}

//All completed rides have a payment
fact AllCompletedRidesHavePayments {
	all r: Ride | r.rideStatus = COMPLETED
		<=> (one p: Payment | r.payment = p)
}

//All completed rides have a destionation and an end time
fact CompletedRidesHaveDestEnd {
	all r: Ride | r.rideStatus = COMPLETED
		<=> (one r.endTime and one r.finalLocation)
}

//If a ride has an end time, it must have a destination
fact NoEndDestWithoutEndTime {
	all r: Ride | no r.endTime <=> no r.finalLocation
}

//No two rides with the same payment
fact NoRidesWithSamePayment {
	no disj r1, r2: Ride | r1.payment = r2.payment
}

//No two reservations with the same fees
fact NoReservationsWithSameFee {
	no disj r1, r2: Reservation | (r1.fee = r2.fee
		and r1.isExpired = True and r2.isExpired = True)
}

//No couple <ride, reservation> that share a pay-transaction
fact noRideAndResWithCoincidingFeeAndPayment {
	no r: Ride, res: Reservation | (r.payment = res.fee
		and res.isExpired = True)
}

//No payment is not associated to any pay-transaction
fact NoIsolatedPayment {
	no p: Payment | ((no res: Reservation | res.fee = p)
		and (no r: Ride | r.payment = p))
}

//No two coinciding but distinct positions
fact NoPositionOverlapping {
	no disj p1, p2: Position |
		(p1.latitude = p2.latitude and p1.longitude = p2.longitude)
}

//No two distinct coinciding users
fact UniqueUser {
	no disj u1, u2: User | (u1 != u2 and
		(u1.email = u2.email or
		u1.idCardNumber = u2.idCardNumber or
		u1.taxCode = u2.taxCode or
		u1.licenseIdNumber = u2.licenseIdNumber))
}

//No two active reservations by the same user
fact UniqueReservation {
	no disj res1, res2: Reservation | (res1 != res2 and
		(res1.reservedUser = res2.reservedUser
		and res1.isActive = True
		and res2.isActive = True))
}

//Only one active reservation per RESERVED car
fact OnlyOneActiveResPerCar {
	all c: Car | c.status = RESERVED
		<=> (one r: Reservation | r.isActive = True
		and r.reservedCar = c)
}

//No users with a locked account have active reservations
fact NoLockedUserActiveReservation {
	no res: Reservation | (res.isActive = True
		and res.reservedUser.isAccountLocked = True)
}

//No two distinct cars with the same car code
fact UniqueCarCode {
	no disj c1, c2: Car | (c1 != c2 and c1.carCode = c2.carCode)
}



//No two cars in the same position
fact NoCarPositionOverlapping {
	no disj c1, c2: Car | c1.carPosition = c2.carPosition
}

//No two users in the same position
fact NoUserPositionOverlapping {
	no disj u1, u2: User | u1.userPosition = u2.userPosition
}

//There can not be two rides for the same user that overlap in time
fact NoOverlappingRidesPerUser {
	all disj r1, r2: Ride | 
		(r1.reservation.reservedUser = r2.reservation.reservedUser)
		implies
		(r1.endTime < r2.startTime or r2.endTime < r1.startTime)
}

//No two distinct rides with the same associated reservation
fact NoDisjRidesWithSameReservation {
	no disj r1, r2: Ride | r1.reservation = r2.reservation
}

//All charging stations are within the Safe Area
fact PowerGridInsideSafeArea {
	all pgs: PowerGridStation | pgs.location in SafeArea.coverage
}

//No two power grids in the same position
fact NoPowerGridOverlapping {
	no disj pg1, pg2: PowerGridStation |
		pg1.location = pg2.location
}

//Conditions of AUTHENTICATED rides
fact NoAuthRideWithCarNotInUse {
	all r: Ride | r.rideStatus = AUTHENTICATED
		<=> r.reservation.reservedCar.status = INUSE
}

//No AUTHENTICATED ride has a payment (yet)
fact NoPaymentIfAuthRide {
	no p: Payment | (some r: Ride | r.payment = p
								and r.rideStatus = AUTHENTICATED)
}

//All pending pay-transactions correspond to an locked users
fact AllPendingRidePaymentsHaveLockedUser {
	all r: Ride | r.payment.isPending = True
		<=> (r.reservation.reservedUser.isAccountLocked = True)
}

fact AllPendingReservationFeesHaveLockedUser {
	all r: Reservation | r.fee.isPending = True
		<=> (r.reservedUser.isAccountLocked = True)
}

//No locked user can have an AUTHENTICATED ride
fact NoLockedUserWithAuthRide {
	all u: User | u.isAccountLocked = True
		implies (no r: Ride | (r.rideStatus = AUTHENTICATED
						and r.reservation.reservedUser = u))
}

//No locked user can have an active reservation
fact NoLockedUserWithActiveReservation {
	all u: User | u.isAccountLocked = True
		implies (no res: Reservation | (res.isActive = True
						and res.reservedUser = u))
}

//If a ride is not expired nor active, there is an associated ride
fact NoUnexpiredReservationWithoutRide {
	all res: Reservation |
		(res.isExpired = False and res.isActive = False)
		<=> (one r: Ride | r.reservation = res)
}

//Account locked <=> (pending payment XOR pending fee)
fact NoTwoPendingPaymentsWithSameUser {
	all u: User | u.isAccountLocked = True <=>
		(((one r: Ride | r.payment.isPending = True and r.reservation.reservedUser = u)
		and (no res: Reservation | res.fee.isPending = True and res.reservedUser = u))
		or
		((no r: Ride | r.payment.isPending = True and r.reservation.reservedUser = u)
		and (one res: Reservation | res.fee.isPending = True and res.reservedUser = u)))
}

//There are not locked users that have no reservations at all
fact LockedUsersHaveAtLeastOneReservation {
	all u: User | u.isAccountLocked = True
		implies (some r: Reservation | r.reservedUser = u)
}

//All reservations correspond to a RESERVED car
fact AllReservationsHaveOneReservedCar {
	all r: Reservation | r.isActive = True 
		<=> r.reservedCar.status = RESERVED
}

//------------ASSERTIONS------------

//An AUTHENTICATED ride must not have a payment
assert NoAuthRideWithPayment {
	no r: Ride, p: Payment | r.payment = p
		and r.rideStatus = AUTHENTICATED
}

//A COMPLETED ride must have a destination and end time
assert RideCompleted {
	all r: Ride | (r.rideStatus = COMPLETED) <=>
		(one r.endTime and one r.finalLocation)
}

//There must be no rides with expired reservations
assert NoRideIfReservationExpired {
	no r: Ride | (r.reservation.isExpired = True)
}

//An AUTHENTICATED ride must not have a destination and
//		end time
assert NoEndTimeFinalDestForAuthRides {
	all r: Ride | r.rideStatus = AUTHENTICATED <=>
		(no r.endTime and no r.finalLocation)
}

//There must be no two authenticated rides for the same user
assert NoTwoAuthRidesSameUser {
	no disj r1, r2: Ride |
		(r1.reservation.reservedUser = r2.reservation.reservedUser
			and r1.rideStatus = AUTHENTICATED
			and r2.rideStatus = AUTHENTICATED)
}

//All cars INUSE must be unlocked
assert AllInUseCarsAreUnlocked {
	all c: Car | c.status = INUSE
		implies c.isLocked = False
}

pred show() {}

run show for 5

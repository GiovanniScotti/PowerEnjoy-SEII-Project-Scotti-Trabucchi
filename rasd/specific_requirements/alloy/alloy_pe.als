open util/boolean

//UNIX time notation is used
//Dates are calculated as the number of seconds from the 1st of January 1970

//SIGNATURES

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

sig Car {
	carCode: one Int,
	status: one CarStatus,
	batteryLevel: one BatteryLevel,
	isLocked: Bool,
	isEngineOn: Bool,
	isOnCharge: Bool,
	carPosition: one Position,
} {
	carCode > 0
	status = AVAILABLE implies batteryLevel = HIGH
	status = RESERVED implies batteryLevel = HIGH
	status = INUSE implies not (batteryLevel = EMPTY)
	batteryLevel = EMPTY implies status = OUTOFSERVICE
	isOnCharge = True implies isLocked = True
	isOnCharge = True implies (one pg: PowerGridStation | pg.location = carPosition)
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
	isActive: Bool, //a Reservation is active until the car becomes "INUSE"
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

	reservation.isActive = False
	reservation.isExpired = False

	originLocation in SafeArea.coverage
	not (finalLocation in SafeArea.coverage)
		implies (reservation.reservedCar.status = OUTOFSERVICE)
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
	totalAmount: one Int,
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

//FACTS

fact CompletedRidesHaveDestEnd {
	all r: Ride | r.rideStatus = COMPLETED <=> (one r.endTime and one r.finalLocation)
}

fact NoEndDestWithoutEndTime {
	all r: Ride | no r.endTime <=> no r.finalLocation
}

//No two rides with the same payment
fact NoRidesWithSamePayment {
	no disj r1, r2: Ride | r1.payment = r2.payment
}

//No payment is not associated to any transaction
fact NoIsolatedPayment {
	no p: Payment | ((no res: Reservation | res.fee = p)
		or (no r: Ride | r.payment = p))
}

//No two coinciding but distinct positions
fact NoPositionOverlapping {
	no disj p1, p2: Position | (p1.latitude = p2.latitude and p1.longitude = p2.longitude)
}

//No two distinct coinciding users
fact UniqueUser {
	no disj u1, u2: User | (u1 != u2 and
		(u1.email = u2.email or u1.idCardNumber = u2.idCardNumber or
		u1.taxCode = u2.taxCode or u1.licenseIdNumber = u2.licenseIdNumber))
}

//No two active reservations by the same user
fact UniqueReservation {
	no disj res1, res2: Reservation | (res1 != res2 and
		(res1.reservedUser = res2.reservedUser and res1.isActive = True
		and res2.isActive = True))
}

//TODO: stessa macchina, al massimo una reservation/ride per volta

//TODO: stesso user, no due ride nello stesso momento?

//No users with a locked account have active reservations
fact NoBlockedUserReservation {
	no res: Reservation | (res.isActive = True
		and res.reservedUser.isAccountLocked = True)
}

fact UniqueCarCode {
	no disj c1, c2: Car | (c1 != c2 and c1.carCode = c2.carCode)
}

//Describes AVAILABLE cars conditions
fact AvailableForRentCar {
	all c: Car | (c.status = AVAILABLE)
		implies (c. isLocked = True and c.isEngineOn = False
			and c.carPosition in SafeArea.coverage and 
			(no r: Reservation | r.reservedCar = c and r.isActive = True))
}

//describes RESERVED cars conditions
fact ReservedCar {
	all c: Car | (c.status = RESERVED)
		implies ((one res: Reservation | res.reservedCar = c 
							and (no r: Ride | r.reservation = res)
			and res.isActive = True)
			and c.isEngineOn = False)
}

//Describes INUSE cars conditions
fact InUseCar {
	all c: Car | (c.status = INUSE)
		implies (c.isLocked = False and c.isOnCharge = False
			and (one r: Ride | r.rideStatus = AUTHENTICATED
						and r.reservation.reservedCar = c))
}

//Describes OUTOFSERVICE cars conditions
fact OutOfServiceCar {
	all c: Car | (c.status = OUTOFSERVICE)
		implies (c.isEngineOn = False and
						(no res: Reservation | res.isActive = True
							and res.reservedCar = c))
}

//No two cars in the same position
fact NoCarPositionOverlapping {
	no disj c1, c2: Car | c1.carPosition = c2.carPosition
}

//No two users in the same position
fact NoUserPositionOverlapping {
	no disj u1, u2: User | u1.userPosition = u2.userPosition
}

fact NoOverlappingRidesPerUser {
	all disj r1, r2: Ride | 
			(r1.reservation.reservedUser = r2.reservation.reservedUser)
			implies (r1.endTime < r2.startTime or r2.endTime < r1.startTime)
}

fact NoDisjRidesWithSameReservation {
	no disj r1, r2: Ride | r1.reservation = r2.reservation
}

fact PowerGridInsideSafeArea {
	all pgs: PowerGridStation | pgs.location in SafeArea.coverage
}

//No two power grids in the same position
fact NoPowerGridOverlapping {
	no disj pg1, pg2: PowerGridStation | pg1.location = pg2.location
}

//No rides with expired reservations
assert NoRideIfReservationExpired {
	no r: Ride | (r.reservation.isExpired = True)
}

assert RideCompleted {
	all r: Ride | (r.rideStatus = COMPLETED) <=>
		(one r.endTime and one r.finalLocation)
}

assert NoEndTimeFinalDestForAuthRides {
	all r: Ride | r.rideStatus = AUTHENTICATED <=>
		(no r.endTime and no r.finalLocation)
}

fact NoPaymentIfAuthRide {
	all r: Ride | r.rideStatus = AUTHENTICATED <=>
		(no r.payment)
}

//Reservation expiration implies payment (fee)
//fact ReservationExpirationPayment {
//	all res: Reservation, p: Payment | (res.isExpired = True) implies
//		(one p.payRes and p.payRes = res)
//}

//DOVREBBE FUNZIONARE
//User account locked if pending payment
fact PendingPaymentsLockAccounts {
	all p: Payment | p.isPending = True
		<=> ((one res: Reservation | res.fee = p and
						res.reservedUser.isAccountLocked = True)
			or (one r: Ride | r.payment = p and
						r.reservation.reservedUser.isAccountLocked = True))
}

pred show() {
	//Funziona
	//some r: Reservation | r.isExpired = True
	//some u: User | u.isAccountLocked = True
	some r: Ride | r.rideStatus = COMPLETED
}

run show for 4

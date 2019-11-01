abstract sig Bool{}

one sig True extends Bool{}

one sig False extends Bool{}

sig FiscalCode{}

sig ThirdPartyId{}

sig Username{}

sig Password{}

sig Registration{
    username: one Username,
    password: one Password
}

abstract sig AccessRights{}

--See the list of my reports (User)
one sig MySignalViolations extends AccessRights{}

--See unsafe areas (User and Municipal Employee and Municipal Director and Police Officer)
one sig UnsafeAreaAnalysis extends AccessRights{}

--Make a report (User)
one sig SignalViolation extends AccessRights{}

--See all violations (Police Officer and Municipal Director)
one sig CheckViolations extends AccessRights{}


--Validate Signalations (Police Officer)
one sig ValidateSignalViolations extends AccessRights{}

--See Statistics (Municipal Director)
one sig Statistics extends AccessRights{}

abstract sig Customer{
    registration: one Registration,
    accessRights: set AccessRights,
}

sig User extends Customer{
    fiscalCode: one FiscalCode,
    mySignalations: set Signalation
}

abstract sig ThirdParty extends Customer{
    id: one ThirdPartyId,
    municipal : one Municipality
}

sig Municipality{
    violations: set Violation
}

sig Signalation{
    violation: one Violation,
    spotter: one User,
}

sig PoliceOfficer extends ThirdParty{
    listSignalations: set Signalation 
}

sig MunicipalEmployee extends ThirdParty{
}

sig MunicipalDirector extends ThirdParty{
    listViolations: set Violation
}

sig Location{
    latitude: one Int,
    longitude: one Int
}
{latitude >= -3 and latitude <= 3 and longitude >= -6 and longitude <= 6}

sig LicensePlate{}

sig TimeStamp{}

sig Violation{
    id: one Int,
    licensePlate: one LicensePlate,
    location: one Location,
    spotter: one User,
    timestamp: one TimeStamp,
    isValid: one Bool,
    municipality: one Municipality
}

sig Ticket{
    amount: one Int,
    signalation: one Signalation,
    policeOfficer: one PoliceOfficer 
}
{amount >=0}

------------------------------------------------------------------------------------------------------------

--All Registrations have to be associated to one Customer
fact RegistrationCustomer{
    all r : Registration | some c : Customer | r in c.registration
}

--The Registration has a unique Customer
fact NoSameRegistration{
    no disj c1,c2 : Customer | c1.registration = c2.registration
}

--All Usernames have to be associated to a Registration
fact UsernameRegistration{
    all u : Username | some r : Registration | u in r.username
}

--All Passwords have to be associated to a Registration
fact PasswordRegistration{
    all p : Password | some r : Registration | p in r.password
}

--Every Customer has a unique username
fact NoSameUsername{
    no disj c1,c2 : Customer | c1.registration.username = c2.registration.username
}

--All FiscalCodes must be associated to a User
fact FiscalCodeMustBeAssociatedToUser{
    all f : FiscalCode | some u : User | f in u.fiscalCode
}

--All ThirdPartyId must be associated to a ThirdParty
fact ThirdPartyIdMustBeAssociatedToTHirdParty{
    all i : ThirdPartyId | some t : ThirdParty | i in t.id
}

--The Fiscal Code can be associated to only one user
fact OneUserFiscalCode{
    no disj u1,u2 : User | u1.fiscalCode = u2.fiscalCode
} 

--The id can be associated to only one third party
fact OneThirdPartyUserId{
    no disj t1, t2 : ThirdParty | t1.id = t2.id
}

--All LicensePlates have to be associated to a Violation
fact LicenseViolation{
    all l : LicensePlate | some v : Violation | l in v.licensePlate
}

--All Timestamps have to be associated to a Violation
fact TimestampViolation{
    all t : TimeStamp | some v : Violation | t in v.timestamp
}

--All Violations have to be associated to a Signalation
fact ViolationSignalation{
    all v : Violation | some s : Signalation | v in s.violation
}

--Only one id per violation, no replicas!
fact OneIDViolation{
    no disj v1,v2 : Violation | v1.id = v2.id
}

--It is not possible to have two different locations with the same plate and timestamp
fact SamePlateLocationAndTimestamp {
    all v1,v2 : Violation | 
    v1.location = v2.location implies (v1.licensePlate = v2.licensePlate and v1.timestamp = v2.timestamp)
}

fact PoliceOfficerRights{
    all p : PoliceOfficer | CheckViolations in p.accessRights and ValidateSignalViolations in p.accessRights and UnsafeAreaAnalysis in p.accessRights
}

fact UserRights{
    all u : User | MySignalViolations in u.accessRights and UnsafeAreaAnalysis in u.accessRights and SignalViolation in u.accessRights
}

fact MunicipalEmployeeRights{
    all me : MunicipalEmployee | UnsafeAreaAnalysis in me.accessRights
}

fact MunicipalDirectorRights{
    all md : MunicipalDirector | UnsafeAreaAnalysis in md.accessRights and CheckViolations in md.accessRights and Statistics in md.accessRights
}


--Police Officer sees all and only the violations of his Municipality of competence
fact PoliceSeeViolations{
    all p : PoliceOfficer | all s : Signalation | p.municipal = s.violation.municipality implies s in p.listSignalations    
}

--Police Officer sees all and only the violations of his municipality of competence
fact PoliceDontSeeViolations{
    all p: PoliceOfficer | all s: Signalation | p.municipal != s.violation.municipality implies s not in p.listSignalations
}

--Municipal Director sees all the violations of his municipality of competence
fact MunicipalDirectorSeeViolations{
    all md : MunicipalDirector | all v : Violation | md.municipal = v.municipality implies v in md.listViolations 
}

--All Signalations are referred to one User
fact SignalationCorrespondToOneUser{
    all s : Signalation | all u : User | (s in u.mySignalations implies s.spotter = u) and (s.spotter = u implies s in u.mySignalations) 
}

--Each Violation is referred to only one Municipality
fact ViolationOneMunicipality{
    all v : Violation | all disj m1,m2 : Municipality | v.municipality = m1 implies v not in m2.violations  
}

--All Violations are referred to Municipality
fact ViolationsOfMunicipality{
    all v : Violation | all m : Municipality | v.municipality = m implies v in m.violations   
}

--All Tickets are referred to a Signalation of the Municipality of the Police Offer who erogates the ticket
fact TicketSameMunicipalityPoliceOfficer{
    all t : Ticket | t.signalation.violation.municipality = t.policeOfficer.municipal 
}

--All Tickets are referred to a Signalation of a valid Violation
fact TicketsForValidViolation{
    all t : Ticket | t.signalation.violation.isValid = True
}

--All Municipalities are referred to a Third Party or Violation
fact MunicipalityToThirdPartyOrViolation{
    all m : Municipality | some t : ThirdParty | m in t.municipal
}

----------------------------------------------------------------------------------------------------------------------------------

--Different Police Officer of the same Municipality see the same violations
assert DifferentOfficerSameViolations{
    all disj p1, p2 : PoliceOfficer | all s1 : p1.listSignalations | all s2 : p2.listSignalations | p1.municipal = p2.municipal 
    implies (s1 in p2.listSignalations and s2 in p1.listSignalations) else (s1 not in p2.listSignalations and s2 not in p1.listSignalations)
}

check DifferentOfficerSameViolations for 10

--All the signalations are present in the list of violations of the Police Officer
assert SignalationPresentInTheList{
    all s : Signalation | all p : PoliceOfficer | s.violation.municipality = p.municipal implies s in p.listSignalations
}

check SignalationPresentInTheList for 10

--All Tickets refer to a signalation of the list signalations of the Police Officer
assert TicketFromPoliceOfficer{
    all t : Ticket | all s : Signalation | some p : PoliceOfficer | s in t.signalation implies s in p.listSignalations 
}
check TicketFromPoliceOfficer for 10

assert TicketOnlyTrueViolation{
    no t : Ticket | t.signalation.violation.isValid = False
}
check TicketOnlyTrueViolation for 10

pred world1{
    #PoliceOfficer >= 3
    #User = 2
    (some disj p1,p2,p3 : PoliceOfficer | p1.municipal = p2.municipal and p1.municipal != p3.municipal)
}
run world1 for 10 but 0 Ticket, 0 Bool, 0 Signalation, 0 Violation, 0 AccessRights

/*
From the first world in Figure ? it can be noticed that every Police Officer has a different Id, every User has a different
FiscalCode and every Username is different from another. Both Users and Third Parties can share the password and there can be 
many Police Officer in the same Municipality, same analogy is for MunicipalDirector and MunicipalEmployee 
*/

pred world2{
    #PoliceOfficer = 2
    #Signalation = 2
    #Ticket >= 1
    one s : Signalation | s.violation.isValid = False
    one s : Signalation | s.violation.isValid = True
}
run world2 for 10 but 0 AccessRights

/*
From the second world in Figure ? it can be noticed that there are two Violations, one it's a real violation that it doesn't tampered
(so it has True as 'isValid') and the other one it's a fake violation that it has tampered (so it has False as 'isValid'). The ticket 
genereated by the Police Officer is for only the real violation (omitting all the checks that led to 'true') and not for the other one.
Moreover, the ticket is generated only one time (in this case by PoliceOfficer0 and not also by PoliceOfficer1 of the same Municipality) 
*/

pred world3{
    #PoliceOfficer = 2
    #User = 2
    #MunicipalDirector = 1
    #MunicipalEmployee = 2
}
run world3 for 10 but 0 Ticket, 0 Bool, 0 Signalation, 0 Violation

/*
From the third world in Figure ? it can be noticed that every PoliceOfficer have the same accessRights as well as all the Users have the 
same accessRights and so on. Classes of accessRights have been created for a reason of granularity: in this way the accessRight can change 
in the future or can be added and the application keeps track of the privilege of everyone.
*/

pred world4{
    #PoliceOfficer = 2
    #MunicipalDirector = 1
    #User.mySignalations >=1
    all disj p1,p2 : PoliceOfficer | one d : MunicipalDirector | all s : Signalation | p1.municipal = p2.municipal and p1.municipal = d.municipal 
    and (s in p1.listSignalations implies (s in p2.listSignalations))
    and (s in p1.listSignalations implies (s.violation in d.listViolations))
    and (s in p2.listSignalations implies (s in p1.listSignalations))
    and (s.violation in d.listViolations implies (s in p1.listSignalations))
}
run world4 for 10 but 0 Ticket
/*
From the fourth world in Figure ? it can be noticed that every signalation is present on the list of signalation of every PoliceOfficer of
the same Municipality and the MunicipalDirector sees the violations in his list of violations of all the signalations of his Municipality of
competence
*/ 
abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

--'checked' will be 1 after the verification of the system
sig FiscalCode{
    name: one String,
    checked: Bool
}

sig Email{
    name: one String,
    checked: Bool
}

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
{#MySignalViolations >= 1}

--See unsafe areas (User and Municipal Employee and Municipal Director and Police Officer)
one sig UnsafeAreaAnalysis extends AccessRights{}
{#UnsafeAreaAnalysis >= 1}

--Make a report (User)
one sig SignalViolation extends AccessRights{}
{#SignalViolation >= 1}

--See all violations (Police Officer and Municipal Director)
one sig CheckViolations extends AccessRights{}
{#CheckViolations >= 1}

--Validate Signalations (Police Officer)
one sig ValidateSignalViolations extends AccessRights{}
{#ValidateSignalViolations >= 1}

--See Statistics (Municipal Director)
one sig Statistics extends AccessRights{}
{#Statistics >= 1}

abstract sig Customer{
    registration: one Registration,
    accessRights: some AccessRights,
    email: one Email
}

sig User extends Customer{
    fiscalCode: one FiscalCode,
}

sig ThirdParty extends Customer{
    id: one ThirdPartyId
}
--------Do we really need them?
sig PoliceOfficer extends ThirdParty{
    tickets: some Ticket
}

sig MunicipalEmployee extends ThirdParty{}

sig MuniciaplDirector extends ThirdParty{}
--------------------------------------
sig Location{
    latitude: one Int,
    longitude: one Int
}
{latitude >= -90 and latitude <= 90 and longitude >= -180 and longitude <= 180}

sig HardEvidence{}

--'checked' will be 1 after the verification of the system
sig LicensePlate{
    name: one String,
    checked: Bool
}

sig TimeStamp{}

sig Violation{
    id: one Int,
    licensePlate: one LicensePlate,
    location: one Location,
    spotter: one User,
    timestamp: one TimeStamp,
    hardEvidence: some HardEvidence,
    isValid: one Bool
}

sig Ticket{
    amount: one Int,
    id: one String,
    violation: one Violation,
    policeOfficer: one PoliceOfficer 
}

--All FiscalCodes must be associated to a User
fact FiscalCodeMustBeAssociatedToUser{
    all f : FiscalCode | some u : User | f in u.fiscalCode
}

--All ThirdPartyId must be associated to a ThirdParty
fact ThirdPartyIdMustBeAssociatedToTHirdParty{
    all i : ThirdPartyId | some t: ThirdParty | i in t.id
}

--All Emails must be associated to a Customer
fact EmailMustBeAssociatedToCustomer{
    all e : Email | some c: Customer | e in c.email
}

--Every Customer has a unique username and email
fact NoSameUsernameOrEmail{
    no disj c1,c2: Customer | c1.registration.username = c2.registration.username or c1.email = c2.email
}
--The Fiscal Code can be associated to only one user
fact OneUserFiscalCode{
    no disj u1,u2 : User | u1.fiscalCode = u2.fiscalCode
} 

--The Fiscal Code must be valid and belonging to the user
fact OnlyValidFiscalCode{
    all u: User | u.fiscalCode.checked = 1
}

--The Email must be valid and belonging to the user
fact OnlyValidEmail{
    all c: Customer | c.email = 1
}

--The id can be associated to only one third party
fact OneThirdPartyUserId{
    no disj t1, t2 : ThirdParty | t1.id = t2.id
}

--All Usernames have to be associated to a Registration
fact UsernameRegistration{
    all u: Username | some r: Registration | u in r.username
}

--All Passwords have to be associated to a Registration
fact PasswordRegistration{
    all p: Password | some r: Registration | p in r.password
}

--All Registrations have to be associated to a Customer
fact RegistrationCustomer{
    all r: Registration | some c: Customer | r in c.registration
}

--All LicensePlates have to be associated to a Violation
fact LicenseViolation{
    all l: LicensePlate | some v: Violation | l in v.licensePlate
}

--All Timestamps have to be associated to a Violation
fact TimestampViolation{
    all t: TimeStamp | some v: Violation | t in v.timestamp
}

--The LicensePlates must be valid (with correct syntax)
fact CorrectLicense{
    all l: LicensePlate | l.checked = 1
} 
--Only one id per violation, no replicas!
fact OneIDViolation{
    no disj v1, v2 : Violation | v1.id = v2.id
}

--It is not possible to have two different locations with the same plate and timestamp
fact SamePlateLocationAndTimestamp {
    all v1, v2 : Violation | 
    v1.location = v2.location implies (v1.licensePlate = v2.licensePlate and v1.timestamp = v2.timestamp)
}

fact PoliceOfficerRights{
    all p: PoliceOfficer | some cv : CheckViolations | some val : ValidateSignalViolations | 
    some ar : UnsafeAreaAnalysis | cv in p.accessRights and val in p.accessRights and ar in p.accessRights
}

fact UserRights{
    all u : User | some my : MySignalViolations | some ar : UnsafeAreaAnalysis | some sv : SignalViolation |
    my in u.accessRights and ar in u.accessRights and sv in u.accessRights
}

fact MunicipalEmployeeRights{
    all me: MunicipalEmployee | some ar : UnsafeAreaAnalysis | ar in me.accessRights
}

fact MuniciaplDirectorRights{
    all md : MuniciaplDirector | some ar : UnsafeAreaAnalysis | some ck : CheckViolations | some st : Statistics |
    ar in md.accessRights and ck in md.accessRights and st in md.accessRights
}

# CivicSense Bhutan

Streamlit and SQLite prototype for citizen complaint reporting and municipal triage in Thimphu. Citizens can register,
submit complaints with optional photos, track their own complaint tokens and status, and update their accounts.
Administrators use a separately authenticated dashboard to review and manage all complaints.

## Run

```powershell
python -m venv .venv
.\.venv\Scripts\Activate.ps1
pip install -r requirements.txt
streamlit run app.py
```

The app uses `civicsense.db` and `uploads/` beside `app.py` by default. It creates and seeds an empty database with
the prototype's historical sample complaints. Existing complaint rows are retained; startup performs additive
SQLite migrations for account ownership and analysis/audit metadata. There is no reset control in the app.

## Accounts and access

- Citizens create accounts in the app. Passwords are stored as salted PBKDF2-HMAC-SHA256 hashes. Citizens can read
  only complaints owned by their account and can update their profile and password from **Account** in the sidebar.
  After successful signup, the app returns to the citizen sign-in screen.
- Administrators have a separate sign-in and signup screen. A signed-in administrator can open **Add admin** in
  the vertical sidebar, enter the new administrator's username, and generate a username-bound one-time invite.
  The code is valid for 24 hours, stored only as a hash, and can be redeemed once; a new invite from that
  administrator invalidates their previous unused invite. Share both the assigned username and code privately.
  Successful signup returns to the administrator sign-in screen. Administrator passwords must contain at least
  16 characters and are stored as salted
  PBKDF2-HMAC-SHA256 hashes. For first-time setup, an operator can still configure an invite code and/or operator
  credentials on the server:

  ```powershell
  $env:CIVICSENSE_ADMIN_USERNAME = "municipal-admin"
  $env:CIVICSENSE_ADMIN_PASSWORD = "<use-a-long-unique-secret>"
  $env:CIVICSENSE_ADMIN_SIGNUP_CODE = "<optional-bootstrap-code-of-at-least-32-characters>"
  streamlit run app.py
  ```

  Use a deployment secret manager rather than committing credentials or putting them in source control. The
  operator-managed admin password is compared server-side and is not stored in the SQLite account table. The
  dashboard-generated invite is stored as a hash in SQLite and does not require environment configuration.
- Both roles have an **Account** page in the sidebar. Citizens can edit their username, name, phone, and password.
  Administrators can edit their username, display name, and contact phone, and change the password for an app-registered
  administrator account. Changing a username preserves owned complaints and administrator attribution. Server-provisioned
  administrator credentials must be changed by the service operator.
- Citizen and administrator profiles can each choose a saved **System**, **Light**, or **Dark** appearance. System follows
  the device or browser color-scheme preference.
- Sidebar navigation uses labeled buttons in a compact 17rem expanded width, without separate sidebar labels or status text.
  The app toolbar is minimized.
- Existing complaints have no citizen account owner and are visible only to administrators.

## Triage and AI configuration

The offline engine is a transparent weighted-keyword classifier with conservative rule-based urgency. Critical and
high-risk terms take precedence; unfamiliar complaints default to Medium rather than Low. Low is used only for
known complaint categories with explicit low-impact wording. `Category Score` is a weighted local keyword-match score,
not a percentage or a calibrated model confidence.
Complaint receipts and saved complaint details show the weighted score and matched terms for each category, so staff
can see how the local classifier selected its result.

An optional hosted model can return structured category/urgency analysis and explanations. Configure exactly one
provider on the server:

```powershell
$env:CIVICSENSE_AI_PROVIDER = "OpenAI"  # or Anthropic or Groq
$env:OPENAI_API_KEY = "<server-side-secret>"
```

Use `ANTHROPIC_API_KEY` or `GROQ_API_KEY` for those providers. The report description is sent for triage only when the
citizen opts in on the submit page. The API key stays server-side. Invalid model responses, API errors, and timeouts
fall back to local triage without blocking submission. A model-reported confidence is displayed only when the response
contains a valid 0-1 value; it is explicitly not independently calibrated. The app does not include or download a
trained model, so a hosted provider and API key are required for model-based analysis.

## Location and photos

The app recognizes nine configured Thimphu landmarks in complaint text and can extract a likely place phrase after
common location cues. Citizens can enter a freeform place name without blocking submission. With explicit consent,
the app can search either the typed location or the extracted phrase using OpenStreetMap Nominatim; only that place
string is sent, not the full complaint or contact details. Searches are rate-limited to one per second, cached in
process memory, and restricted to the supported Thimphu map area. Results require the citizen to select the intended
place; the system does not guess among multiple matches. If search fails, the entered/extracted name is still saved
and the complaint has no guessed coordinates; it is omitted from the map and geographic duplicate matching.

Photos are stored under `uploads/`. The upload field clears after a complaint is successfully committed to SQLite;
on a submission error, the selected photo remains available for retry. An administrator can explicitly authorize an
AI photo review for a selected complaint; that action sends the photo and complaint description to the configured
vision-capable provider and saves the generated review for both the citizen and administrators to see. AI reviews
describe visible evidence and limitations and should not be treated as definitive safety assessments. AI photo review
requires a configured provider and API key.

## Administration and limitations

Administrators can search and filter all complaints, inspect descriptions and photos, update status and reviewed
urgency, view original triage urgency, and export CSV/Excel. Administrators can request AI service insights based on
aggregate complaint counts, categories, priorities, locations, and statuses; only these summary aggregates are sent to
the configured provider, not citizen names, contact details, or free-text complaint descriptions. Citizens can remove
their own complaints and administrators can remove any complaint, one at a time from the complaint list. Selecting
Remove opens a confirmation prompt; the complaint is deleted only after confirmation. Removal also deletes the stored
photo when it is inside `uploads/`. The admin map includes all complaints with known coordinates, including resolved
reports, and automatically fits the map to all markers so locations such as Babesa are visible on load. Selecting a
marker shows the original citizen report. Reports without coordinates are listed below the map and are not assigned
guessed locations.
The receipt's Print token button opens the browser print dialog and prints only the complaint token.
The OpenStreetMap map tiles require internet access.

This remains a single-process Streamlit/SQLite proof of concept, not a production identity platform. It does not
provide email/phone verification, centralized login throttling, multi-instance session management, or deployment
hardening. Before production use, deploy behind HTTPS and a trusted identity/access layer, protect the SQLite file
and uploaded photos, configure backups, and review the data-retention and AI-provider privacy requirements.
Officer names and phone numbers in the seed data are illustrative.

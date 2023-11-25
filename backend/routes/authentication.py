import os
import json
import requests
from flask import Blueprint, session, redirect, request, jsonify
from flask_restful import Resource
from flask_login import current_user, login_user, logout_user

from config import app, db, api
from db.models import User

from oauthlib.oauth2 import WebApplicationClient

# Configuration for Google OAuth 2.0
GOOGLE_CLIENT_ID = os.environ.get("GOOGLE_CLIENT_ID", None)
GOOGLE_CLIENT_SECRET = os.environ.get("GOOGLE_CLIENT_SECRET", None)
GOOGLE_DISCOVERY_URL = "https://accounts.google.com/.well-known/openid-configuration"

os.environ['OAUTHLIB_INSECURE_TRANSPORT'] = '1' # TODO: Remove this line in production. This is to allow localhost to use https

client = WebApplicationClient(GOOGLE_CLIENT_ID)

# Blueprint for authentication
auth = Blueprint('auth', __name__)


def get_google_provider_cfg():
  """Gets the Google provider configuration."""
  return requests.get(GOOGLE_DISCOVERY_URL).json()

# Resources for authentication
class CheckSession(Resource):
  """Checks if the user is logged in."""
  def get(self):
    if current_user.is_authenticated:
      return current_user.to_dict(), 200
    return {'error': '401 Unauthorized'}, 401

class Logout(Resource):
  """Logs the user out."""
  def delete(self):
    if current_user or session['user_id']:
      logout_user
      return {'message': 'Logged out successfully'}, 204
    return {'error': '401 Unauthorized'}, 401
 
# Routes for authentication 
@auth.route('/api/login')
def login():
    google_provider_cfg = get_google_provider_cfg()
    authorization_endpoint = google_provider_cfg["authorization_endpoint"]
    request_uri = client.prepare_request_uri(
        authorization_endpoint,
        redirect_uri=request.base_url + "/callback",
        scope=["openid", "email"],
    )
    return redirect(request_uri)
  
# Callback for authentication 
@app.route("/api/login/callback")
def callback():
  code = request.args.get("code") 

  google_provider_cfg = get_google_provider_cfg()
  token_endpoint = google_provider_cfg["token_endpoint"]

  # Prepare and send a request to get tokens. 
  token_url, headers, body = client.prepare_token_request(
      token_endpoint,
      authorization_response=request.url,
      redirect_url=request.base_url,
      code=code,
  )

  token_response = requests.post(
      token_url,
      headers=headers,
      data=body,
      auth=(GOOGLE_CLIENT_ID, GOOGLE_CLIENT_SECRET),
  )
  
  # Parse the tokens!
  client.parse_request_body_response(json.dumps(token_response.json()))

  # Now that we have tokens. Find and hit the URL
  userinfo_endpoint = google_provider_cfg["userinfo_endpoint"]
  uri, headers, body = client.add_token(userinfo_endpoint)
  userinfo_response = requests.get(uri, headers=headers, data=body)

  # We want to make sure their email is verified. 
  # The user authenticated with Google, authorized our app, and now we've verified their email through Google!
  if userinfo_response.json().get("email_verified"):
      unique_id = userinfo_response.json()["sub"] # A Google-issued ID token from the user.
      users_email = userinfo_response.json()["email"]
  else:
      return {"error": "User email not available or not verified by Google"}, 400

  # Create a user in our db with the information provided by Google
  # we need to check what infornation we can store in our db
  user = User(
      id=unique_id, email=users_email
  )

  # Doesn't exist? Add it to the database.
  if not User.get(unique_id):
      user = User(
          id=unique_id, email=users_email
      )
      db.session.add(user)
      db.session.commit()

  # Begin user session by logging the user in 
  db_user = User.get(unique_id)
  login_user(db_user, remember=True) # Handle remember me functionality
  return redirect("http://localhost:5173/")
  
api.add_resource(CheckSession, '/check_session', endpoint='check_session')
api.add_resource(Logout, '/logout', endpoint='logout')

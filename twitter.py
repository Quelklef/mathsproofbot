import tweepy
import time
import os
import json

from main import prove



def get_auth():

  if os.path.exists('auth.json'):
    with open('auth.json', 'r') as f:
      creds = json.loads(f.read())
  else:
    creds = {}

  if 'consumer_key' not in creds:
    creds['consumer_key'] = input('Twitter API Consumer Key: ')

  if 'consumer_secret' not in creds:
    creds['consumer_secret'] = input('Twitter API Consumer Secret: ')

  auth = tweepy.OAuthHandler(creds['consumer_key'], creds['consumer_secret'])

  if 'access_token' not in creds:
    auth_url = auth.get_authorization_url()
    print('Go here: ' + auth_url)
    verifier = input('Verifier Pin: ')
    auth.get_access_token(verifier)
    creds['access_token'] = auth.access_token
    creds['access_token_secret'] = auth.access_token_secret

  auth.set_access_token(creds['access_token'], creds['access_token_secret'])

  with open('auth.json', 'w') as f:
    f.write(json.dumps(creds))

  return auth

auth = get_auth()
api = tweepy.API(auth)

def reply_to_tweet(tweet_id, response):
  """
  Reply to a tweet.
  Return the reply's tweet object.
  """
  return api.update_status(
    status = response,
    in_reply_to_status_id = tweet_id,
    auto_populate_reply_metadata = True,
  )

def get_timeline(user_id):
  return tweepy.Cursor(
    api.user_timeline,
    user_id = user_id,
    tweet_mode='extended',
  ).items()

# == # == # ==

def blen(string):
  """
  Return the number of bytes, which seems to be
  how Twitter counts length
  """
  return len(bytes(string, encoding='utf-8'))

def chunk_280(string):
  """
  Split a long string into chunks which are 280 characters or less.
  Chunks will not split lines.
  If a line is over 280 characters, an exception will be thrown.
  """

  lines = string.split('\n')

  if any(blen(line) > 280 for line in lines):
    raise ValueError('A line with length >280 was given') 

  chunk = []
  while lines:
    while lines and blen('\n'.join(chunk + [lines[0]])) <= 280:
      chunk.append(lines.pop(0))
    yield '\n'.join(chunk)
    chunk = []

def long_reply_to_tweet(tweet_id, response):
  """
  Reply to a tweet, splitting it over several replies
  if it's longer than 280 characters.
  Lines will not be split.
  """
  chunks = chunk_280(response)
  for chunk in chunks:
    tweet = reply_to_tweet(tweet_id, chunk)
    tweet_id = tweet.id

def prove_tweet(tweet_id, tweet_text):
  """
  For a tweet that contains a logical proposition, try to
  prove the proposition and reply to the tweet with the proof.
  If we can't prove the proposition (read: it takes too long),
  just return without doing anything.
  """
  print('Got a new theorem to prove: ' + tweet_text)
  proof = prove(tweet_text)
  proof = 'Proof:\n\n' + proof
  print(proof if proof is not None else 'failed to prove')
  if proof is None:
    return
  long_reply_to_tweet(tweet_id, proof)

def already_proven(status):
  """
  Did we already prove a status?
  We assume that if we've replied to a tweet, then we've proven it.
  """
  our_tweets = get_timeline(our_id)
  return any(
    status.id == our_tweet.in_reply_to_status_id
    for our_tweet in our_tweets
  )


# == # == # == #


our_id = '1254278067985383425'
mathslogicbot_id = '2871456406'

class MyStreamListener(tweepy.StreamListener):
  def on_status(self, tweet):
    if tweet._json['user']['id'] == int(mathslogicbot_id):
      prove_tweet(tweet.id, tweet.text)

def listen_to_mathslogicbot():
  listener = MyStreamListener()
  stream = tweepy.Stream(auth=auth, listener=listener)
  print('Listening to @mathslogicbot...')
  stream.filter(follow=[mathslogicbot_id])

def prove_from_mathslogicbot_timeline():
  timeline = get_timeline(mathslogicbot_id)
  for status in timeline:
    if already_proven(status):
      print(f"Already proved {status.full_text}")
    else:
      prove_tweet(status.id, status.full_text)

if __name__ == '__main__':

  import sys
  import traceback

  if len(sys.argv) != 2 or sys.argv[1] not in ['--prove-existing', '--listen']:
    print('please call with --prove-existing or --listen')
    quit()

  with open('log.log', 'a') as log_f:

    while True:
      try:
        if sys.argv[1] == '--listen':
          listen_to_mathslogicbot()
        else:
          prove_from_mathslogicbot_timeline()
      except KeyboardInterrupt as e:
        break
      except Exception as e:
        s = traceback.format_exc()
        print(s)
        log_f.write(s)

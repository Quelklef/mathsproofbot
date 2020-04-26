
import tweepy
# if it doesn't exist, create a twitter_auth.py with the following 4 values
from twitter_auth import consumer_key, consumer_secret, access_token, access_token_secret
from prove import prove

auth = tweepy.OAuthHandler(consumer_key, consumer_secret)
auth.set_access_token(access_token, access_token_secret)
api = tweepy.API(auth)

def reply_to_tweet(tweet, response):
  return api.update_status(
    status = response,
    in_reply_to_status_id = tweet.id,
    auto_populate_reply_metadata = True,
  )

def chunk_280(string):
  """
  Split a long string into chunks which are
  280 characters or less.
  Chunks will not split lines.
  If a line is over 280 characters, an exception will be thrown.
  """

  lines = string.split('\n')

  if any(len(line) > 280 for line in lines):
    raise ValueError('A line with length >280 was given') 

  chunk = []
  while lines:
    while lines and len('\n'.join(chunk + [lines[0]])) <= 280:
      chunk.append(lines.pop(0))
    yield '\n'.join(chunk)
    chunk = []

def long_reply_to_tweet(tweet, response):
  """
  Reply to a tweet, splitting it over several replies
  if it's longer than 280 characters.
  Lines will not be split.
  """
  chunks = chunk_280(response)
  for chunk in chunks:
    tweet = reply_to_tweet(tweet, chunk)


class MyStreamListener(tweepy.StreamListener):
  def on_status(self, tweet):
    print('Got a new theorem to prove: ' + tweet.text)
    proof = prove(tweet.text)
    long_reply_to_tweet(tweet, 'Proof:\n' + proof)

if __name__ == '__main__':
  listener = MyStreamListener()
  stream = tweepy.Stream(auth=auth, listener=listener)
  mathslogicbot_id = '2871456406'
  stream.filter(follow=[mathslogicbot_id])


